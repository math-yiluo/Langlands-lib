# The top derivative surjects onto the standard upper-unipotent coinvariants

Author: Worker 784. This module is an internal prerequisite of the exact proof task
`62de5903-b616-4b5c-88eb-a066b77c5467`, which proves
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. It is the rank-zero
top-localization comparison (`k = 0`, target `GL_0`) of that task's arrangement. The
positive two-block comparison remains with Worker 357 and is not touched here.

## Statement

Fix `p`, a `PadicField F`, supplied topological data `T`, and
`ψ : UnitaryAdditiveCharacter F.Carrier` for `T.topology`. Let `N > 0` and let `A` be a
smooth complex representation of `GL_N(F)`. Its carrier lives in an arbitrary universe
`uV`, independent of the field universe `uF`.

`finite_coinvariants_of_topDerivative T ψ N hk hpos A` says: if the published top
derivative `(Derivative.generalLinearDerivative T ψ N N hk).obj A` is finite
dimensional, then so is

```text
Jacquet.Localization.Coinvariants A.representation (upperUnipotent N F.Carrier)
  (entrywiseCharacter ψ.complex N)
```

Here `entrywiseCharacter ψ.complex N` is the published all-ranks character of
[`EntrywiseCharacter`](EntrywiseCharacter.md). In positive rank it is
`u ↦ ψ(∑ u_(i,i+1))`, by `entrywiseCharacter_apply_sum`; in rank one it is trivial. The
quotient is by the span of `A(u)v - θ_ψ(u) v`. No irreducibility, admissibility or
supercuspidality is assumed.

## Source

Bernstein–Zelevinsky (1976), §5.15, printed page 49 (source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`). There the
representation `(Φ⁻)^(n-1)(π)` of `P_1 = {e}` is said to be realized in `E_(U,Θ)`, by the
quotient-in-stages rule §2.32. This module proves the direction needed for finiteness:
a surjective linear map from the top derivative onto `E_(U,θ_ψ)`. It does not prove that
the map is injective.

## The derivative and its normalization

By the published definitions in [`Derivative/Iteration`](../Derivative/Iteration.md),
`generalLinearDerivative T ψ N N hk` is the rank transport along
`N = (N - N) + (N - 1) + 1` (`generalLinearDerivative_of_pos`), followed by
`generalLinearDerivativePositive T ψ 0 (N - 1)`. That functor is restriction to the
mirabolic `P_N`, then `N - 1` normalized functors `Φ⁻`, then the normalized `Ψ⁻` to `GL_0`:

- Each `Φ⁻ : P_(j+2) → P_(j+1)` localizes at the radical character `θ_ψ` of the last
  column, the published `mirabolicTheta`. It then twists the descended successor action
  by `|det|^(-1/2)` (`phiMinus_action`). `phiMinusCharacter_eq_one_of_upper` proves that
  this determinant normalization is `1` on upper unipotent matrices. The twist therefore
  plays no role on `U`.
- The last functor is `Ψ⁻ : P_1 → GL_0`. `P_1` is the trivial group (published
  `rankOne_eq_one`), so its radical acts trivially and its relations vanish. This is the
  rank-one boundary. For `N = 1` there are no `Φ⁻` steps and the top derivative is the
  `Ψ⁻` quotient of the restriction to `P_1`.

## Proof

- `entrywiseCharacter_radical`: on radical columns the entrywise character equals the
  published `theta ψ n`. Both are `ψ` of the last column entry, by the published
  `superdiagonalSum_radical`.
- `entrywiseCharacter_successor`: the successor embedding `diag(-, 1)` of
  [`UpperUnipotentCharacterFactorization`](UpperUnipotentCharacterFactorization.md)
  preserves the entrywise character, since it only adds the zero entry `(n, n+1)`.
- `descend T ψ W j X f hf`, by induction on `j`. Let `X` be a smooth representation of
  `P_(j+1)` (written `mirabolic (0 + j)`) and `f : X →ₗ[ℂ] W` a linear map with
  `f(X(u)v) = θ_ψ(u) f(v)` for all `u ∈ U_(j+1)`. Then `f` factors through the composite
  quotient map `X → Ψ⁻(Φ⁻)^j X`. That composite is the published `iterateQuotient`
  followed by `psiMinusQuotient`.
  - In the base case `j = 0`, `P_1` is trivial and `f` descends through the `Ψ⁻`
    relations.
  - In the inductive step, `f` first kills the `θ_ψ`-relations of the radical. Then the
    descended map satisfies the same hypothesis for `U_(j+1)` acting on `Φ⁻ X`, by the
    two character lemmas and the triviality of the determinant twist. The induction
    hypothesis applies to it.
- `finite_coinvariants_of_derivativePositive`: apply `descend` to the restriction of `B`
  on `GL_(0+n+1)` and to the quotient map onto the `θ_ψ`-coinvariants. This gives a linear
  map from `(generalLinearDerivativePositive T ψ 0 n).obj B` that composes with the
  surjection from `B`, so it is surjective, and finite dimensionality passes along it.
- `finite_coinvariants_of_topDerivative` removes the published rank transport. It
  rewrites with `generalLinearDerivative_of_pos`, then substitutes the rank equations
  `N - N = 0` and `N = 0 + (N - 1) + 1` in a private auxiliary lemma.

## Dependencies

The imports are [`UpperUnipotentCharacterFactorization`](UpperUnipotentCharacterFactorization.md),
which imports the published
[`SupercuspidalDerivativeVanishing`](../Classification/SupercuspidalDerivativeVanishing.md)
for `iterateQuotient`, and the published [`EntrywiseCharacter`](EntrywiseCharacter.md).
Nothing here uses `SupercuspidalDerivatives`, multiplicity one, Kirillov theory, the
target finiteness statement or any of its consumers.
