# Gluing actual projective evaluation morphisms

This is derived infrastructure for the projectivized evaluation construction.
It combines the actual local morphisms of `EvaluationMorphism`, their proved
restriction law in `EvaluationRestriction`, the dual-frame projective
transition law in `FrameBundle`, and Mathlib's gluing theorem for locally
directed open covers. No external assertion or new representability premise
is introduced.

Fix schemes `X` and `S` in a common arbitrary universe `u`, a morphism
`p : X → S`, a module sheaf `M` on `S` locally free of rank `n + 1`, a
line bundle `L` on `X`, and a module-sheaf morphism `ev : M → p_* L`.
The proposition `FrameEvaluationGenerates` says that, for each frame open
`U`, the actual evaluated sections of the chosen frame generate the
pulled-back line bundle on `p⁻¹U` pointwise: at each point, at least one
section has nonzero residue-field value.

Under this explicit hypothesis, `evaluationChartMap` composes the actual
local evaluation morphism over `p⁻¹U` with the chart into
`frameBundle M n hM`. The lemma `evaluationChartMap_restrict` proves

`(p⁻¹U → p⁻¹V) ≫ evaluationChartMap(V) = evaluationChartMap(U)`

for every inclusion of frame opens `U ≤ V`. The proof first applies the
actual smaller-open compatibility of the evaluated sections and their
projective morphisms. It then changes the chosen frame on `U` to the
restriction of the frame on `V`. The resulting dual-frame projective
action cancels against the proved chart transition of the frame bundle.
Thus compatibility of these actual local maps is proved from evaluation;
it is not supplied as gluing data.

The cover `evaluationCover` is the categorical pullback of the locally
directed frame cover along `p`. Its component over `U` is canonically
isomorphic to the actual open subscheme `p⁻¹U`.
The lemma `evaluationCover_trans` identifies each cover transition with
the actual inverse-image-open inclusion under these canonical
isomorphisms. The proof cancels the target open immersion and uses the
cover transition equation. Composing `evaluationChartMap` with the
canonical comparison gives `evaluationCoverMap`.
Its directed compatibility follows by cancelling the source comparison
isomorphism and using the two preceding compatibility lemmas.

The actual global scheme morphism

`evaluationMap : X → frameBundle M n hM`

is defined by `glueMorphismsOfLocallyDirected` for those maps.
The cover computation `evaluationMap_cover` is the gluing theorem's
component equation; transporting it through the canonical comparison
gives `evaluationMap_chart` on the actual inverse-image open.
The local projection equation follows from `localEvaluationMap_toBase`,
`FrameBundle.chart_toBase`, and the equation for the actual restricted
structure map. Checking on the pulled-back frame cover then proves

`evaluationMap ≫ FrameBundle.toBase hM = p`.

Finally, `evaluationMap_unique` proves that any scheme morphism with the
displayed actual chart equations equals `evaluationMap`. It uses
extensionality on the pulled-back frame cover and its canonical
comparison with the inverse-image opens.

All schemes and maps here are actual schemes and scheme morphisms.
There is no affine, noetherian or abelian-scheme hypothesis.
Pointwise generation of the displayed evaluated sections remains an
explicit hypothesis; it is not proved for the abelian-scheme application.
This unit constructs and characterizes a global morphism. It does not
establish its immersion properties, identify its pullback of the
tautological line bundle, or prove the host large-level representability
statement.
