# Descent of the fibrewise-isogeny criterion from strictly Henselian DVRs

This is an internal reduction toward the unchanged arbitrary-base reductive
fibrewise-isogeny statement. `DvrFibrewiseIsogenyStatement.{u}` restricts that
criterion to spectra of all commutative domain DVRs in the same arbitrary
universe. These DVRs have no Henselian, residue-field, excellence, completeness,
or characteristic hypothesis.

`isogeny_of_fpqc_baseChange` reflects the isogeny property of a specified
homomorphism along a flat, surjective, quasi-compact morphism of schemes.
The published `baseChange_map_isPullback` identifies the underlying map of the
base-changed homomorphism with a pullback of the original underlying map.
The projection from its target is fpqc. The proof descends finiteness, flatness,
and surjectivity through that square using the published fpqc descent instances.
No smoothness or reductivity is needed for this reflection.

`isogeny_of_faithfullyFlat_baseChange` specializes reflection to a faithfully
flat ring extension. Mathlib's `flat_and_surjective_SpecMap_iff` supplies
flatness and surjectivity of the spectrum map; its affineness supplies
quasi-compactness.

`isogeny_of_strictHenselian_dvr_cover` assumes both a faithfully flat extension
to a strictly Henselian domain DVR and the strictly Henselian fibrewise-isogeny
criterion. It transports reductivity and the fibrewise condition to the
extension, applies the supplied criterion there, and descends the resulting
isogeny of the specified homomorphism.

`dvrFibrewiseIsogeny_of_strictHenselian_and_extension` uses the separately
declared `StrictHenselianDvrExtensionStatement` to obtain such an extension
for each original DVR. Both the extension existence and the strictly Henselian
isogeny criterion are explicit hypotheses; this module proves neither input.

`IsFibrewiseIsogeny.isDvrwiseIsogeny` then evaluates a supplied DVR criterion
at every DVR-valued point of an arbitrary scheme, using base-change
preservation of reductivity and of the fibrewise-isogeny condition.
`isogeny_of_fibrewise_of_dvr_criterion` combines this with the published
noetherian affine DVR reduction to prove the criterion over a noetherian
affine base, conditional on that DVR criterion.

The results are derived from the named Library constructions and descent
theorems. They do not prove the arbitrary-base target or provide noetherian
approximation.
