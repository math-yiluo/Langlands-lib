# Assembling an actual fppf Picard atlas from the stack inputs

Author: Worker 509.

This internal assembly combines the published proof of full fpqc descent
for actual line bundles and the published smooth relative automorphism
schemes over a proper field scheme with three explicit proposition inputs:
`FieldPicardStackAtlasStatement`, `SmoothAutomorphismEtaleAtlasStatement`,
and `FieldEtaleFppfClassSheafStatement`. These three propositions remain
hypotheses throughout this module.

`fieldEtalePicardAtlas_of_stackInputs` applies the quotient proposition
to the actual relative Picard pseudofunctor. Its fpqc stack hypothesis is
discharged by `lineBundleFpqcStack`, and its smooth automorphism hypothesis
by `PicardGroupoid.field_hasSmoothRelativeAutomorphismSchemes`. Properness
over the arbitrary field supplies the latter theorem's hypothesis.
The smooth stack atlas is supplied by the first explicit input.
The result is scheme representability of the full etale class-sheaf
diagonal and an etale-surjective scheme atlas locally of finite type
over the field.

`fieldPicardAlgebraicSpaceAtlas_of_stackInputs` uses the third explicit
input to obtain the full canonical natural isomorphism from etale to fppf
class sheaves. The published atlas transport theorem composes the etale
atlas transformation with this isomorphism and transports representability
of the diagonal. Its conclusion is algebraic-space representability of
the published actual fppf class sheaf and existence of a locally finite
type etale-surjective scheme atlas. The definition `fieldFppfPicardAtlas`
chooses such an actual scheme and transformation, with proofs of their
three geometric properties.

Every construction concerns all schemes over the field and all sheaf
sections, including sections without global line-bundle representatives.
The universe `u`, the field, and the proper scheme are arbitrary.
No hypothesis of projectivity, smoothness, reducedness, connectedness,
a section, a universal bundle, or identification of global functions
with the field is introduced.

This is derived support from the imported Library results, with no new
external assertion or source. It does not prove the three input
propositions, closedness of the Picard diagonal, or the exact
`FieldPicardSheafAlgebraicSpaceStatement`. The conditional conclusions
therefore do not complete the host proof task.
