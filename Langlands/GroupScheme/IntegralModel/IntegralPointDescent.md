# Descent of the original integral-point image

This internal construction uses the existing equivalence between actual affine
scheme points and homomorphisms from their global coordinate algebra. It retains
the supplied integral model and its original generic-fibre isomorphism.

Let `R` be a commutative domain with fraction field `K`, let `G` be a group
scheme over `K`, and let `M : IntegralModel R K G` be the supplied affine model
with its specified generic identification. All coefficient rings and fields
belong to the same arbitrary universe `u`.

`integralSectionOfCoordinates` constructs an actual original integral section
from a rational point `g` whenever every original-model coordinate, transported
to `G` using `M.genericCoordinate`, evaluates in the image of `R → K`.
`integralPointMap_integralSectionOfCoordinates` proves that this section maps to
the original `g`. Consequently,
`mem_integralPoints_iff_genericCoordinates` characterizes membership in the
original subgroup by precisely this coordinate condition. The generic
identification is always the supplied `M.genericIso`.

For the extended criterion, take a commutative domain `A` with fraction field
`L`, maps `R → A` and `K → L`, and compatible algebra structures on `L`.
The scalar-tower hypotheses assert that the square commutes.
`mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates` characterizes
the integral image of `M.baseChange A L` in the original group's `L`-coefficient
points: every original-model generic coordinate must take its value in the
image of `A → L`.

Suppose, in addition, that for every `x : K`,

```
algebraMap K L x ∈ Set.range (algebraMap A L)
  ↔ x ∈ Set.range (algebraMap R K).
```

This is the explicit intersection condition that the inverse image of the
extended integral ring inside `L` is the original integral ring inside `K`.
`mem_integralPoints_rationalExtend_iff` then proves that the existing
`rationalExtend K L G g` belongs to the extended integral-point subgroup exactly
when `g` belongs to `M.integralPoints`.
`integralPoints_eq_comap_baseChange` expresses the same result as an equality of
the original subgroup with the comap of the extended subgroup under that
existing homomorphism.

The private affine lifting construction restricts the point's coordinate
homomorphism to the range of an injective coefficient map. It composes with the
inverse algebra equivalence from that range to the source and applies the
published affine scheme-point equivalence. Evaluation proves that changing
coefficients recovers the original point. The original-model recovery lemma
projects the generic point through the actual pullback, cancels
`M.genericIso.hom` against its inverse, and uses the projection formula for
`baseChangeSectionHom`. The extended criterion reuses the published
`mem_baseChange_coefficientIntegralPoints_iff`; the reflection theorem then
uses naturality of actual regular-function evaluation and applies the
intersection equivalence coordinate by coordinate.

This is an internal construction from published affine coordinate and
integral-model base-change interfaces, with Mathlib's algebra range
equivalence. It invokes no additional literature assertion. It requires no
smoothness, reductivity, topology, Galois extension, or residue-field
restriction. The intersection hypothesis remains explicit. This is only a
point-descent step: it constructs no canonical model, special point, building,
metric, or equality with a building stabilizer, and it does not prove the
unconditional `BuildingComparisonStatement`.
