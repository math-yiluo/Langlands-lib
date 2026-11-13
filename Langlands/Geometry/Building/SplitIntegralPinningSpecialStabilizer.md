# The special point of the integral subgroup of a split integral pinning

Module `Langlands.Geometry.Building.SplitIntegralPinningSpecialStabilizer`.

## Statement

`IntegerValuationBuildingData.exists_isSpecialPoint_eq_oneStabilizer_of_pinning`.
Let `k` be a field with a valuation `v : Valuation k ℤₘ₀` whose valuation ring has an
infinite residue field, let `G` be an affine group scheme over `k`, and let
`B : IntegerValuationBuildingData v G`. Let `i : S → G` be a maximal split torus of `G`
that is also a maximal torus, with `i` a monomorphism on underlying schemes, let
`P : SplitIntegralPinning v i`, and let `ν` be a generic cocharacter of `i` such that every
`g ∈ G(k)` is a product `κ p` with `κ ∈ P.K` and `p` a rational point of the dynamic
parabolic of `ν ≫ i`. Then there is a point `x` of the reduced building of `B` such that

* `x` is a special point of `B`,
* `P.K = B.oneStabilizer x`, the one-group stabilizer `G(k)^1 ∩ G(k)_x`, and
* every point `y` of the reduced building fixed by all of `P.K` equals `x`.

The torus `i` is not assumed to be the torus of `B`.

## Proof

1. By conjugacy of maximal split tori (`maximalSplitTorusConjugacy`, Borel–Tits 4.21)
   there are `g ∈ G(k)` and `e : B.S ≅ S` with `B.i ≫ int(g) = e ≫ i`.
2. Transport `B` along `(e, int(g))` with `basedTransport` (module
   `IntegerValuationBuildingBasedTransport`); the result `B'` has torus exactly `i`.
3. `P.toFrame` is a split integral frame on `B'`, so
   `exists_isSpecialPoint_K_eq_oneStabilizer` gives a point `x₀` of the apartment of `B'`
   at which every root value of the frame vanishes, with `B'.apartmentMap x₀` special and
   `P.K = B'.oneStabilizer (B'.apartmentMap x₀)`. The unit with square different from one
   comes from `exists_unit_sq_ne_one` (infinite residue field).
4. The Library's `KPApartmentData.conjugateReducedBuildingEquiv` identifies the reduced
   building of `B'` with that of `B` by `q ↦ g · q'`, where `q'` is the preimage of `q`
   under the comparison of step 2; this identification is `G(k)`-equivariant for the
   original action and preserves fixers (`reducedFixer_conjugateReducedBuildingEquiv`).
   Let `x` be the image of `B'.apartmentMap x₀`.
5. `x` is special: the preimage of `B'.apartmentMap x₀` is special by
   `isSpecialPoint_basedTransport_iff`, and special points are stable under `G(k)`
   (`IsSpecialBuildingPoint.smul`). The one-group stabilizers agree because the fixers
   agree and `G(k)^1` does not depend on the building data.
6. Uniqueness: if `y` is fixed by `P.K`, its preimage in the building of `B'` is fixed by
   `P.K` by equivariance, so it equals `B'.apartmentMap x₀` by
   `SplitIntegralFrame.eq_apartmentMap_of_forall_smul_eq_of_infinite`; hence `y = x`.

## Provenance

This packages Bruhat–Tits II, Propositions 4.6.28(i), 4.6.29(i) and 4.6.31 (special
point, its one-group stabilizer, and uniqueness of the fixed point) in the form needed
for a split integral pinning supplied on a torus different from the torus of the
building data; all mathematical input comes from the Library results named above.
