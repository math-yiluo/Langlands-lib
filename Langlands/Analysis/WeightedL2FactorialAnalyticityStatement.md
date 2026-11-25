# Real analyticity from weighted factorial L² bounds

`Langlands.Analysis.WeightedL2FactorialAnalyticityStatement d` is an internal
proposition for every natural dimension `d`, including zero. Its domain is
`EuclideanSpace ℝ (Fin d)` with its Euclidean norm, standard orthonormal basis
and standard volume. Its values are complex and its derivatives and analyticity
are over the real scalars.

Let `F` be smooth on the open ball `ball x₀ R`, with `R > 0`. Smoothness is
`ContDiffOn ℝ ∞`; the scoped `∞` means genuine smoothness, not the analytic
level `ω`. For each derivative order `k`, let

`T_k(y) = √(∑_{w : Fin k → Fin d} ‖D^k F(y)(e ∘ w)‖²)`.

Here `D^k` is Mathlib's iterated Fréchet derivative and every ordered word is
counted once. The empty word is retained at order zero. The premise supplies
one pair of real constants `C, A`, independent of `k`, such that

`sup_{R/2 ≤ ρ < R} (R - ρ)^k ‖T_k‖_{L²(ball x₀ ρ)} ≤ ofReal(C A^k k!)`.

The supremum and L² norms are extended nonnegative reals. Real weights enter
through `ENNReal.ofReal`; the constants need no separate sign hypotheses.
The conclusion is `AnalyticAt ℝ F x₀`. This is a statement, not a proof.
It asserts no bound for solutions of a differential equation.

This internal assembly interface follows the ordered-word conventions of the
cutoff estimates (`LocalEllipticCutoffEstimate`) and of the local Sobolev
estimate (`LocalSobolevPointwise`). The premise is written explicitly using
Mathlib alone, so the statement does not depend on the cutoff,
Sobolev and factorial-derivative proof modules. Its weighted supremum is exactly
`ballWeightedSeminorm (derivWordNorm k F) x₀ R k` when those separately defined
conventions are unfolded. No PDE or elliptic regularity theorem is imported
or assumed implicitly.
