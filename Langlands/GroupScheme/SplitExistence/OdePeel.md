# Solutions of root-operator ODEs are ordered products of root exponentials

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.OdePeel`, namespace `LieRootData`.

## Declarations

- `divExp_mul_divExp_neg` and `divExp_neg_mul_divExp`: `x_k(f) x_k(-f) = 1 = x_k(-f) x_k(f)`.
- `ode_peel h` (**ODE peeling**). Let `A` be a torsion-free commutative `ℚ`-algebra and
  `h : X →+ ℤ`. Let `Ψ` be a finite set of roots on which `h` is positive, and which is closed in
  the following sense: if `a, b ∈ Ψ`, `m ≥ 1` and `root θ = root a + m • root b`, then `θ ∈ Ψ`.
  Let `M` lie in the `A[X]`-span of the `E_θ`, `θ ∈ Ψ`, and let `c` be a matrix over `A[X]` with
  `c' = M c` and `c(0) = 1`. Then there is a list `L` of pairs (root in `Ψ`, parameter in
  `A[X]`) such that `c = ∏_{(θ, f) ∈ L} x_θ(f)`. The roots in `L` are pairwise distinct, and their
  `h`-values are nondecreasing along `L`.

Proof (strong induction on `Ψ`): if `Ψ = ∅` then `M = 0`, and `c = 1` by
`eq_one_of_mderiv_eq_zero`. Otherwise pick `ε ∈ Ψ` with minimal `h`-value, and write
`M = m₀ E_ε + M₁` with `M₁` in the span over `Ψ \ {ε}`. Let `F` be the antiderivative of `m₀`
vanishing at `0` (`exists_antideriv`), and set `c₁ = x_ε(-F) c`. Then `c₁(0) = 1` and
`c₁' = (x_ε(-F) M₁ x_ε(F)) c₁` (by `mderiv_divExp`). Conjugation by `x_ε(-F)` keeps `M₁` in the
span over `Ψ \ {ε}` (`conj_mem`, module `LieConj`). This set is again closed, because adding a
positive multiple of a root of `Ψ` strictly raises `h`, so the result is never the `h`-minimal
`ε`. By induction `c₁` is an ordered product over `Ψ \ {ε}` with nondecreasing `h`-values, and
`c = x_ε(F) c₁` puts `ε` in front.

Provenance: internal proof route. This ODE argument replaces the formal power series argument of
Steinberg, *Lectures on Chevalley groups*, §3, for Chevalley's commutator formula.
