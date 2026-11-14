# Radical preimages and integral points of incident models

This internal consequence of published model and parabolic-subgroup results
implements the algebraic transfer needed in the neighbourhood argument for
the depth-zero opposite-factor proof. It works over an arbitrary local domain
`R` with supplied fraction field `K`, at arbitrary universe `u`.

Let `source` and `target` be actual `RelativeComponentModelData R K G`, let
`φ : RelativeComponentModelHom source target` be a compatible model morphism
with identity generic fibre, and let `Q` be supplied
`SpecialFibreQuotientData target`. The direction is the usual one for incident
facets: the model of the larger facet maps to the model of its face.
No facets or building are assumed or constructed here.

`ParabolicRadicalPreimageTransferStatement` says that the following hypotheses
imply `Q.positivePoints ≤ source.neutral.integralPoints`:

- The schematic image of `φ` on neutral special fibres is parabolic.
- The inverse image under target reduction of **all residue-field points of
  that schematic image** is exactly the image of source integral sections.
- `Q.radicalInclusion` represents the ground-field unipotent radical of the
  target neutral special fibre.

The subgroup `Q.positivePoints` is the generic image of integral sections
reducing to rational points of that actual radical. It is not replaced by the
congruence kernel. A reductive quotient property for `Q.projection` is
unnecessary; the represented radical property alone suffices.

`parabolicRadicalPreimageTransfer` proves the statement. Its three supporting
lemmas in `RelativeComponentModelHom` expose the steps:

1. `positivePoints_le_source_of_radicalPoints_le` lifts a target section
   reducing into the schematic image by the exact reduction-preimage equality.
   The identity generic fibre identifies the lifted section's generic point
   with the original one.
2. `radicalPoints_le_specialFibreImagePoints` applies the published
   `IsParabolicSubgroup.radicalFactor` and its compatibility identity. The
   target neutral special fibre is smooth and affine by base change, and
   connected by the supplied connected-fibre property. The radical inclusion
   therefore factors through the parabolic schematic image, giving inclusion
   on rational points.
3. `positivePoints_le_source_of_parabolicReductionPreimage` combines those
   results.

No surjectivity of the map on residue-field rational points is used. The
factorization goes through the schematic image itself, as required by the
definition of `HasParabolicReductionPreimage`.

The provenance is internal: `SpecialFibre`, `ModelMorphism`,
`IntegralModel.ConnectedFibreDescent`, and
`Reductive.ParabolicUnipotentKernel` supply the definitions, connected special
fibre, radical factorization, and generic-point compatibility. This module
derives their integral-point consequence.

For the intended application, one must still construct the actual fixed-point
models, show that nearby models satisfy these parabolic and reduction-preimage
hypotheses, and compare their root integral points with nonnegative restricted
root values. No neighbourhood, root-value comparison, model existence, or
unconditional depth-zero opposite-factor theorem is claimed here.
