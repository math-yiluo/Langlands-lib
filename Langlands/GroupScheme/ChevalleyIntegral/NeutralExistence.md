# Integral existence from smooth closures and full-fibre opens

This internal construction combines the Dedekind neutral-model construction with
the neutral field-isomorphism criterion. Fix a Chevalley datum on the full
coordinate lattices `I → ℤ`, a Dedekind domain `R`, its fraction field `K`, and
a supplied generic Chevalley group `C`. Smoothness of the full integral schematic
closure is an explicit hypothesis.

The supplied generic group is smooth, affine and connected. The existing group
geometry results give geometric connectedness and integrality. Therefore
`exists_dedekindNeutralModel` applies to the smooth closure.
`neutralModelOfSmoothClosure` chooses one actual affine flat finite-type neutral
model, and `neutralInclusionOfSmoothClosure` chooses its inclusion extending the
identity of the generic group. The specification proves that this inclusion
represents the relative identity component and that the chosen model is smooth
with geometrically connected fibres.

`neutralTorusOfSmoothClosure` factors the entire coordinate torus through this
fixed neutral model. It is closed, including in the presence of central
directions or an empty root set. These choices precede the quantification over
field algebras.

The remaining field hypothesis asks, for every field `k` with a supplied
`R`-algebra structure, for a supplied field Chevalley group and a nonempty open
of the **full** field fibre contained in its closed embedding image.
`hasFieldComparisons_neutralModelOfSmoothClosure` applies the existing neutral
open-image criterion to obtain compatible actual field isomorphisms for this
same neutral model and torus.
`exists_neutralRealization_of_fullFieldOpen` packages their affineness, flatness,
local finite presentation, torus closedness and all field comparisons.

Finally, `integralExistence_of_smoothClosure_fullFieldOpen` specializes to
`ULift.{u} ℤ` and its fraction field and invokes the published full-coordinate
normalization and comparison reduction. Its conclusion is the unchanged
`ChevalleyIntegralExistenceStatement.{u}`, conditionally on smoothness of the
chosen integer closures and the stated nonempty full-fibre opens for every
coordinate Chevalley datum. This module does not prove either of these remaining
geometric hypotheses. It assumes no connectedness of the full closure.

The provenance is an internal deduction from `GenericClosure`,
`DedekindNeutralModel`, `NeutralCoordinates`, `NeutralFieldComparison`, and
`ModelComparison`, together with the published smooth connected affine group
geometry. No new external literature assertion is introduced.
