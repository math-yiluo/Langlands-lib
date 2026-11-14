# Galois transport of negative root partners

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.NegativeRootPartnerGalois`.

Setting, as in the Library module `Rational.SteinbergCanonicalGaloisTransport`: fields
`k ⊆ K` in one universe, an affine group scheme `G` over `k`, a commutative group scheme
`T` over `k` with `i : T ⟶ G`, a split pinning `p` of `G_K`, and an isomorphism
`eT : p.torus ≅ T_K` such that `hT : p.inclusion = groupHom eT.hom ≫ i_K`.

## Results

- `NormalizedRootParametrization.negPoint_rationalConjugate` takes `σ : K ≃ₐ[k] K` and
  normalized maps `x` of `a` and `y` of `c`. Assume conjugation by `σ` transports the root
  of `a` to that of `c` (`hroot`, transported through `eT`), and the values of `x` to those
  of `y`: `σ(x(e)) = y(σ e)` for all `e`. Then it transports the negative partners:
  `σ(x.negPoint d) = y.negPoint (σ d)` for all `d`.

  For `d = 0` both sides are `1`. Otherwise put `e = -d⁻¹`, a unit. The pair
  `(x.negPoint d, x.negPoint d)` is an opposite factor pair of `x(e)`
  (`isOppositeFactorPair_rationalPoint`). Transport it to `T_K` (`changeTorus`), conjugate
  it (`IsOppositeFactorPair.rationalConjugate`), rewrite the root by `hroot` and the point by
  the value hypothesis, and transport back (`isOppositeFactorPair_changeTorus_iff`). This
  gives an opposite factor pair of `y(σ e)`. By `eq_negPoint_of_isOppositeFactorPair` it is
  `(y.negPoint (σ d), y.negPoint (σ d))`, since `-(σ e)⁻¹ = σ d`.
- `negPointFamily x a d` (definition): the negative partner `(x a).negPoint d` of a family
  of normalized simple-root maps.
- `RootMapsGaloisCompatible.negPointFamily_rationalConjugate`: for Galois-compatible
  normalized simple-root maps, as in `GaloisCompatiblePinningData`, with the root transport
  `hroot` (field `action_root`),
  `rationalConjugate σ (negPointFamily x a d) = negPointFamily x (ρ σ a) (σ d)`. The value
  hypothesis is `RootMapsGaloisCompatible.rationalPoint` (module
  `Rational.RootMapGaloisRationalPoints`).

## Use

Together with the positive maps, this gives Galois-compatible words for coroot values:
`h_eq_word` of `Algebra.RankOneRelationIdentities` expresses `a^∨(u)` through `x_a(1)`,
`x_a(u⁻¹)`, `y_a(u - 1)` and `y_a(u⁻¹(u - 1))`. This is the input for the orthogonal-orbit
case of the inclusion `Z_G(S)(k) ⊆ G(k)^+` for quasi-split simply connected groups.

## Provenance

Internal; combines published Galois transport and uniqueness of opposite pairs.
