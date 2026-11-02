# Distinct simple reflections of a Coxeter system

`Langlands.Group.RelativeWeylIndexing.simple_injective` proves

\[
\texttt{Function.Injective cs.simple}
\]

for every `B : Type u`, `W : Type v` with `[Group W]`,
`M : CoxeterMatrix B` and `cs : CoxeterSystem M W`. Distinct indices give
distinct simple reflections. Neither `B` nor `W` is assumed finite or
nonempty, and the universes are independent.

## Provenance and scope

This is an internal auxiliary lemma for the
[associated-subset proof](RelativeWeylAssociatedSubsetProof.md), which needs
it to count the associated subset. The pinned Mathlib proves `s_i² = 1`
(`simple_mul_simple_self`) and `ℓ(s_i) = 1` (`length_simple`), but lists the
distinctness of simple reflections only as a TODO in
`Mathlib/GroupTheory/Coxeter/Basic.lean`. The proof below uses a
standard reflection-representation argument. No source text is translated
here, and no faithfulness of the representation is claimed. The module
imports only Mathlib.

## The representation

All definitions are private and `noncomputable`.

* `halfRoot m` is `exp(π i / m)` in `ℂ`.
* `geomCoeff M i j` is `-(h + h⁻¹)/2` with `h = halfRoot (M i j)`, that is
  `-cos(π / M i j)`. Lean's division by zero gives `-1` for `M i j = 0`; this
  case is never used.
* `geomRefl M i` is the linear endomorphism of `B → ℂ` given by
  \[
  (\sigma_i f)(j) = f(j) - 2\,f(i)\,a_{ij},\qquad a_{ij}=\texttt{geomCoeff M i j}.
  \]
  `geomRefl_apply` records this formula.

The coefficients satisfy `a_ii = 1` (`geomCoeff_self`, from `halfRoot 1 = -1`)
and `a_ij = a_ji` (`geomCoeff_symm`, from the symmetry of `M`). If
`M i j = 2`, then `halfRoot 2 = i` and `a_ij = 0` (`geomCoeff_of_two`).

## The Coxeter relations

`geomRefl_isLiftable` proves `M.IsLiftable (geomRefl M)`, that is
`(σ_i σ_j)^(M i j) = 1` for all `i, j`.

* `i = j`: `M i i = 1`, and `geomRefl_mul_self` gives `σ_i² = 1` by a
  coordinate computation using `a_ii = 1`.
* `M i j = 0`: the relation is `A⁰ = 1`.
* `M i j = 2`: `geomRefl_comm` shows that `σ_i` and `σ_j` commute when
  `a_ij = a_ji = 0`, so `(σ_iσ_j)² = σ_i²σ_j² = 1`.
* `M i j ≥ 3` (`geomRefl_pow_of_three`): put `A = σ_iσ_j` and
  `t = 4a_ij² - 2`. A coordinate computation (`geomRefl_cubic`) gives
  \[
  (A^2 - tA + 1)(A - 1) = 0.
  \]
  In `cubic_dvd`, let `m = M i j`, `h = halfRoot m` and `ζ = h²`. Then
  `ζ = exp(2πi/m)` is a primitive `m`-th root of unity
  (`Complex.isPrimitiveRoot_exp`), `t = ζ + ζ⁻¹`, and
  `X² - tX + 1 = (X - ζ)(X - ζ⁻¹)`. Since `m ≥ 3`, the roots `ζ`, `ζ⁻¹` and
  `1` are pairwise distinct. Each is a root of `X^m - 1`, so the pairwise
  coprime linear factors give
  \[
  (X^2 - tX + 1)(X - 1) \mid X^m - 1 .
  \]
  Applying `Polynomial.aeval A` to this divisibility gives `A^m - 1 = 0`.

## Injectivity

`cs.lift ⟨geomRefl M, geomRefl_isLiftable⟩` is a monoid homomorphism from
`W` sending `cs.simple i` to `σ_i`. Suppose `cs.simple i = cs.simple j` with
`i ≠ j`. Apply both images to the indicator function `δ_i = Pi.single i 1`
and evaluate at `i`:

\[
(\sigma_i\delta_i)(i) = 1 - 2a_{ii} = -1,\qquad
(\sigma_j\delta_i)(i) = 1 - 2\,\delta_i(j)\,a_{ji} = 1 .
\]

Since `-1 ≠ 1` in `ℂ`, this is a contradiction.

The Mathlib inputs are `CoxeterSystem.lift` with `lift_apply_simple`, the
complex exponential values `exp(πi) = -1` and `exp(πi/2) = i`, primitive
roots of unity, coprimality of distinct linear factors
(`Polynomial.isCoprime_X_sub_C_of_isUnit_sub`, `IsCoprime.mul_dvd`) and
polynomial evaluation in the algebra `Module.End ℂ (B → ℂ)`.
