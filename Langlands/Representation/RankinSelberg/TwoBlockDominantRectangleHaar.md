# Exact supplied Haar measure for the dominant rectangles

This is internally derived measure data for the rectangles in
Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(2), printed page 419.
The registered original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
In the retained 99-page PDF, printed page 419 is zero-based page 53
(one-based page 54 in the resource reader). The displayed formula was
visually checked.
No source-specific errata record was present in the project or Library notes.
The source displays the rectangle integral; the equivalence, Haar proof,
and total-integral packaging here are derived formalization tools.

For every prime, every `F : PadicField.{uF} p`, and the canonical topology
and Borel measurable structure, `rectangleMeasure F m j k ν` is exactly

```text
(rectangularMeasure ν (m 0 + 1) k).prod
  (rectangularMeasure ν j (m 1 + 1)).
```

It uses the supplied `ν : AdditiveHaarMeasure F.Carrier` throughout.
`rectangleMeasure_eq` exposes that equality by reflexivity. The product
is sigma-finite because the canonical field is second countable and
locally compact, hence every supplied scalar Haar measure is sigma-finite.
Each `rectangularMeasure` is the published nested finite product of this
scalar measure.

The dimensions `j,k` may independently be zero. An empty finite product
has unit mass at the unique empty function. Thus a zero-row or zero-column
rectangle has the Dirac probability measure at its unique zero matrix;
the remaining factor retains its supplied product measure. No division by
a dimension or nonempty-index hypothesis occurs in the proof.

`rectangleChangeHomeomorph` equips the existing actual linear equivalence
`rectangleChange h j k u` with its published continuity and inverse
continuity. Its forward map is `(x,y) ↦ (LA⁻¹*x,y*LB)` and its inverse is
`(x,y) ↦ (LA*x,y*LB⁻¹)`, for the actual `leftMultiplier` and
`rightMultiplier` of an arbitrary actual lower-group element `u`.

`measurePreserving_rectangleChange` proves preservation of the exact
product. The proof first converts the published determinant-one laws
`det_leftMultiplier` and `det_rightMultiplier` into determinant-norm-one
laws. It applies the published `padicRectangularHaarScaling` separately
to left multiplication by `LA⁻¹` and right multiplication by `LB`.
Both scale factors reduce to one. Taking the product of these two
measure-preserving maps gives the actual simultaneous change.
`measurePreserving_rectangleChange_symm` transfers preservation to the
actual inverse through the measurable equivalence.

`integral_rectangleChange` is the corresponding total Bochner identity
for any real normed-space-valued function. `integrable_rectangleChange_iff`
separately proves equivalence of actual integrability in both directions,
using the measure-preserving measurable embedding. Neither result assumes
measurability or integrability of an arbitrary input function. A total
Bochner integral has value zero when its integrand is not integrable;
its value therefore supplies no convergence certificate. These helpers
assert no convergence for the JPSS raw kernel.
