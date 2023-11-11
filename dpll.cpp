#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <list>
#include <sstream>
#include <stack>
#include <string>
#include <vector>

class CNF {
    static unsigned int step;
    static constexpr unsigned int MAX_STEP = -1;

    template <typename T, typename Container = std::list<T>, typename Iterator = typename std::list<T>::iterator>
    class IteratorWrapper {
        Iterator it;
        const Container* pcontainer;

    public:
        IteratorWrapper(Iterator it, const Container* pcontainer)
            : it(it)
            , pcontainer(pcontainer)
        {
            static_assert(std::is_member_function_pointer<decltype(&T::exists)>::value, "T must have a member function exists()");
        }

        T& operator*() { return *it; }
        const T& operator*() const { return *it; }
        T* operator->() { return &*it; }
        const T* operator->() const { return &*it; }

        IteratorWrapper& operator++()
        {
            do {
                ++it;
            } while (it != pcontainer->end() && !it->exists());
            return *this;
        }

        IteratorWrapper operator++(int)
        {
            IteratorWrapper tmp = *this;
            ++*this;
            return tmp;
        }

        bool operator==(const IteratorWrapper& other) const { return it == other.it; }
        bool operator!=(const IteratorWrapper& other) const { return it != other.it; }
    };

    class Literal {
        int val;
        bool negated;
        unsigned int lifetime_start;
        unsigned int lifetime_end;

    public:
        Literal(int val, bool negated, unsigned int lifetime_start = 0, unsigned int lifetime_end = MAX_STEP)
            : val(val)
            , negated(negated)
            , lifetime_start(lifetime_start)
            , lifetime_end(lifetime_end)
        {
        }

        void remove() { lifetime_end = step; }

        void restore()
        {
            if (step == lifetime_end) {
                lifetime_end = MAX_STEP;
            }
        }

        void negate() { negated = !negated; }
        bool exists() const { return step >= lifetime_start && step < lifetime_end; }
        Literal operator!() const { return { val, !negated, lifetime_start, lifetime_end }; }
        bool operator==(const Literal& other) const { return val == other.val && negated == other.negated; }
        operator int() const { return val; }
        int value() const { return negated ? -val : val; }
    };

    class Clause {
        static unsigned int clause_cnt;

        std::list<Literal> literals;
        unsigned int lifetime_start;
        unsigned int lifetime_end;
        unsigned int id;

    public:
        Clause(std::list<Literal> literals, unsigned int lifetime_start = 0, unsigned int lifetime_end = MAX_STEP)
            : literals(literals)
            , lifetime_start(lifetime_start)
            , lifetime_end(lifetime_end)
            , id(clause_cnt++)
        {
        }

        friend class CNF;
        using iterator = IteratorWrapper<Literal, std::list<Literal>, std::list<Literal>::iterator>;
        using const_iterator = IteratorWrapper<const Literal, std::list<Literal>, std::list<Literal>::const_iterator>;

        iterator begin()
        {
            auto it = literals.begin();
            while (it != literals.end() && !it->exists()) {
                ++it;
            }
            return { it, &literals };
        }

        const_iterator begin() const
        {
            auto it = literals.begin();
            while (it != literals.end() && !it->exists()) {
                ++it;
            }
            return { it, &literals };
        }

        iterator end() { return { literals.end(), &literals }; }
        const_iterator end() const { return { literals.end(), &literals }; }
        bool empty() const { return begin() == end(); }
        void remove() { lifetime_end = step; }

        void restore()
        {
            if (lifetime_end == step) {
                lifetime_end = MAX_STEP;
            }
            for (auto& lit : literals) {
                lit.restore();
            }
        }

        bool exists() const { return step >= lifetime_start && step < lifetime_end; }

        int count() const
        {
            int cnt = 0;
            for (auto& lit : literals) {
                if (lit.exists()) {
                    cnt++;
                }
            }
            return cnt;
        }

        bool operator==(const Clause& other) const { return id == other.id; }
    };

public:
    using iterator = IteratorWrapper<Clause, std::list<Clause>, std::list<Clause>::iterator>;
    using const_iterator = IteratorWrapper<const Clause, std::list<Clause>, std::list<Clause>::const_iterator>;

    iterator begin()
    {
        auto it = clauses.begin();
        while (it != clauses.end() && !it->exists()) {
            it++;
        }
        return { it, &clauses };
    }

    const_iterator begin() const
    {
        auto it = clauses.begin();
        while (it != clauses.end() && !it->exists()) {
            it++;
        }
        return { it, &clauses };
    }

    iterator end() { return { clauses.end(), &clauses }; }
    const_iterator end() const { return { clauses.end(), &clauses }; }
    bool empty() const { return begin() == end(); }

    void solve()
    {
        step = 0;
        auto start = std::chrono::high_resolution_clock::now();
        solution_state = solve_impl();
        auto stop = std::chrono::high_resolution_clock::now();
        time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();
    }

    void save_solution(std::string filename) const
    {
        std::ofstream ofs(filename);
        ofs << "s cnf " << solution_state << " " << variable_cnt.size() - 1 << " " << clauses.size() << std::endl;
        ofs << "t cnf " << solution_state << " " << variable_cnt.size() - 1 << " " << clauses.size() << " " << (time_elapsed / 1000.) << " 0" << std::endl;
        if (solution_state == SAT) {
            for (const auto& lit : solution) {
                ofs << "v " << lit.value() << std::endl;
            }
        }
    }

    static CNF from_file(std::string filename)
    {
        std::ifstream ifs(filename);
        std::string line;
        std::list<Clause> clauses;
        std::vector<int> variable_cnt;
        bool valid_header = false;
        int m, n;
        while (std::getline(ifs, line)) {
            if (line[0] == 'c') {
                continue;
            }
            if (line[0] == 'p') {
                std::istringstream iss(line);
                std::string s;
                iss >> s >> s >> n >> m;
                variable_cnt.resize(n + 1);
                valid_header = true;
                continue;
            }
            assert(valid_header);
            std::istringstream iss(line);
            std::list<Literal> literals;
            while (iss >> n) {
                if (n == 0) {
                    clauses.push_back({ literals });
                    literals = {};
                    continue;
                }
                bool negated = n < 0;
                n = std::abs(n);
                literals.push_back({ n, negated });
                variable_cnt[n]++;
            }
        }
        assert(clauses.size() == m);
        return { clauses, variable_cnt };
    }

private:
    std::list<Clause> clauses;
    std::vector<int> variable_cnt;
    std::stack<std::pair<const Literal, unsigned int>> pure_literals;
    std::list<Literal> solution;
    unsigned long long time_elapsed = 0;
    enum state_t {
        UNKNOWN = -1,
        UNSAT = 0,
        SAT = 1
    } solution_state
        = UNKNOWN;

    CNF(std::list<Clause> clauses, std::vector<int> variable_cnt)
        : clauses(clauses)
        , variable_cnt(variable_cnt)
    {
    }

    state_t solve_impl()
    {
        // 0. Prologue: save state
        const auto save_variable_cnt { variable_cnt };
        state_t state = UNKNOWN;
        step++;

        // 1. Unit propagation
        while (unit_propagation()) { }

        // 2. Pure literal elimination
        while (pure_literal_elimination()) {
            if (empty()) {
                state = SAT;
                break;
            }
        }

        // 3. Check if there is an empty clause
        if (state != SAT) {
            for (const auto& clause : clauses) {
                if (clause.exists() && clause.empty()) {
                    state = UNSAT;
                    break;
                }
            }
        }

        // 4. Select a variable, assign truth value, and recurse
        if (state == UNKNOWN) {
            Literal lit { select_variable(), false, step };
            clauses.push_front({ { lit }, step });
            variable_cnt[lit]++;
            state = solve_impl();
            if (state != SAT) {
                clauses.front().begin()->negate();
                state = solve_impl();
            }
            clauses.pop_front();
        }

        // 5. Epilogue: restore state
        if (state == SAT) {
            while (!pure_literals.empty()) {
                solution.push_back(pure_literals.top().first);
                pure_literals.pop();
            }
        }
        for (auto& clause : clauses) {
            clause.restore();
        }
        while (!pure_literals.empty() && pure_literals.top().second >= step) {
            pure_literals.pop();
        }
        step--;
        variable_cnt = save_variable_cnt;
        return state;
    }

    bool unit_propagation()
    {
        bool modified = false;
        for (const auto& clause : *this) {
            if (clause.count() == 1) {
                const auto& unit_lit = *clause.begin();
                for (auto& clause_other : *this) {
                    if (clause_other == clause) {
                        continue;
                    }
                    for (auto& lit : clause_other) {
                        if (lit == !unit_lit) {
                            variable_cnt[unit_lit]--;
                            lit.remove();
                            modified = true;
                        } else if (lit == unit_lit) {
                            for (const auto& l : clause_other) {
                                variable_cnt[l]--;
                            }
                            clause_other.remove();
                            modified = true;
                            break;
                        }
                    }
                }
            }
        }
        return modified;
    }

    bool pure_literal_elimination()
    {
        bool modified = false;
        for (auto& clause : *this) {
            bool is_pure = false;
            for (const auto& lit : clause) {
                if (variable_cnt[lit] == 1) {
                    pure_literals.push(std::make_pair(lit, step));
                    is_pure = true;
                }
            }
            if (is_pure) {
                for (const auto& lit : clause) {
                    variable_cnt[lit]--;
                }
                clause.remove();
                modified = true;
            }
        }
        return modified;
    }

    int select_variable() const
    {
        for (int var = 1; var < variable_cnt.size(); var++) {
            if (variable_cnt[var] > 0) {
                return var;
            }
        }
        assert(false);
    }
};

unsigned int CNF::step = 0;
unsigned int CNF::Clause::clause_cnt = 0;

int main(int argc, char** argv)
{
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <cnf-file>"
                  << " <solution-file>" << std::endl;
        return 1;
    }
    CNF cnf = CNF::from_file(argv[1]);
    cnf.solve();
    cnf.save_solution(argv[2]);
    return 0;
}