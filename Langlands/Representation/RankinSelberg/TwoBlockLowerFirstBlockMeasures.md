# Haar measure in the lower mixed coordinates

This derived support module works with the actual lower mixed subgroup of JPSS,
*Rankin–Selberg convolutions* (1983), Section 4.9, printed pages 416–418. It uses
the canonical topology and valuation of every `PadicField.{uF} p` and retains both
positive block sizes and the published block decomposition. Its construction is
internal measure-theoretic support for the two formulas, rather than a claim
that JPSS explicitly packages a coordinate product as a measurable kernel.

`lowerMixedProductMeasure` transports the product of an arbitrary supplied
rectangular additive Haar measure, the restriction-normalized norm-one first
block Haar, and the fixed second-block unipotent Haar through
`lowerMixedSubgroupHomeomorph`. The coordinate multiplication is
`(Z,a,n)(W,b,m) = (Z + n W a⁻¹, ab, nm)`.

Left multiplication preserves the product: the rectangular affine map preserves
Haar because both diagonal determinants have normalized absolute value one,
and diagonal left translation preserves the fixed product Haar. Right
multiplication is a skew product after swapping the rectangle and diagonal
factors. For each diagonal coordinate its rectangular map is a translation,
while the base map is diagonal right translation. The skew-product theorem
therefore proves right invariance as well. These arguments use the published
coordinate multiplication and `measurePreserving_radicalChange`.

The coordinate homeomorphism preserves compact finiteness and positivity on
nonempty open sets. Together with left invariance these give a Haar measure.
Local compactness and second countability give its regularity. This unit does
not yet assert the mass of the integral points, a common normalization, quotient
compatibility or either integration formula.
