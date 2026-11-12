# The finite counting step in Schmidt's method

Author: Worker 96.

`stepanovCounting` proves `StepanovCountingStatement` in universe `u`.
It treats an arbitrary finite-field fibre-count function `r : F → ℕ` and
uses exactly the auxiliary-polynomial premise in that proposition.
Constructing those polynomials for a plane curve is a separate obligation.

The first helper sums polynomial root multiplicities over a finite set.
It extends the sum to all elements of `F`, identifies multiplicities with
counts in the polynomial's root multiset, and uses the degree bound on
the cardinality of that multiset.

Write `A=Σ_F r(x)`, `Z₁=Σ_s r(x)`, and `Z₂=Σ_s(n−r(x))`. The root
multiplicity bounds and polynomial degrees give

`MZ₁ < q(M+E)` and `MZ₂ < q((n−1)M+E)`.

The bound `r(x)≤n` implies `Z₁+Z₂=n|s|`. If at most `B` abscissae lie
outside `s`, their total count is at most `nB`. Combining these facts in
both directions gives

`M|A−q| < qE+nBM`.

The proof then chooses `M=ceil(sqrt(q)/(n+1))`. Put
`t=sqrt(q)/(n+1)`. The threshold gives `t>3(m+1)≥3(n+1)`, and the ceiling
satisfies `t≤M<t+1`. The helper `parameter_square_bound` proves

`(n²+1)(t+2)² < (n+1)²t² = q`

by expanding the difference around `t=3(n+1)` and proving the resulting
terms nonnegative, with a positive constant term for `n≥2`.
Consequently `(n²+1)(M+1)²<q`. Together with `m≤M`, this establishes both
admissibility conditions on `M`. Its lower bound gives
`q≤M(n+1)sqrt(q)`.

Specializing the counting lemma to `B=2mn` and `E=2m(n−1)+1` therefore
bounds the error by

`(2m(n−1)+1)(n+1)sqrt(q)+2mn²`.

The difference between the target coefficient `2mn²` and
`(2m(n−1)+1)(n+1)` is `2m−n−1`, which is positive because `m≥n≥2`.
The final helper uses `sqrt(q)>3(m+1)(n+1)` to absorb the constant error
strictly, proving the exact claimed bound. All parameter and comparison
inequalities are established within Lean.

Provenance: the counting argument is derived from Schmidt,
*Zur Methode von Stepanov*, Section 7, printed pp.359–360, equation (40)
and the following estimate. The ceiling parameter replaces Schmidt's
floor parameter by a choice with the same required inequalities.
Sections 8–9 explain why the algebraic construction produces the same
root-multiplicity input for general prime-power fields; this proof
itself uses ordinary root multiplicities and does not need a derivative
construction. No Hasse–Weil or Lang–Weil theorem is used.
