# Prescribed full field points for locally finite maps

This internal assembly extends the finite one-chart character lift to a full
field-valued point of the actual saturated presentation. It explicitly assumes
`PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement`; no proof
of that comparison is supplied here.

`StrongHom.HasFieldPointLiftAt g y p` means that there is a full field point
`q` of the source saturated presentation whose underlying point is `y` and
whose image under `FieldPoint.map g` is exactly the prescribed target field
point `p`. Equality includes every containing-chart evaluation.

`FieldPoint.map_toFullRecognitionTarget_eval` computes the evaluation of the
image under `g` followed by target recognition on any recognized target chart
`W`. Given a recognized source chart `V` through the point with image in `W`,
the evaluation equals the recognized source evaluation composed with the
actual full-recognition pair pullback. The proof chooses a local-domain
chart through the source point contained in `V`. Both field-point map
evaluations can use this chart. The identity
`originalRestriction_comp_recognizedSourceExtension` identifies their
pullbacks, proving the claimed formula.

`StrongHom.IsFiniteAt.hasFieldPointLiftAt` assumes finiteness at `y` and a
target field point whose underlying point is `g(y)`. First map this point to
the target full recognition. The finite-character theorem gives a finite
recognized pair through `y` and a character of its source algebra that
restricts exactly to the prescribed evaluation on the target chart.
`FieldPoint.existsUnique_of_chartCharacter`, under the explicit domain
comparison premise, extends this character to a full field point of the
source full recognition. The canonical quasi-isomorphism from the saturated
presentation to full recognition gives its preimage as a field point of
the source saturated presentation.

The image of this preimage and the prescribed target point have the same
ordinary point. After mapping both to target full recognition, the evaluation
formula above shows that they agree on the selected target chart. The
one-chart equality theorem, with the same explicit domain comparison premise,
identifies these full-recognition field points. Injectivity of field-point
mapping along the canonical target quasi-isomorphism gives equality on the
target saturated presentation.

`SaturatedAtlasPresentation.strongEtaleFieldPointImageLift_of_domain` deduces
the strong étale image-lifting proposition from that same domain comparison.
An all-pieces étale strong map is quasifinite, hence finite at every chosen
source point. An ordinary image witness selects such a source point, and the
finite-at-a-point theorem supplies the full prescribed lift.

The ground field, space, chart-index and extension-field universes are
independent in the finite lifting construction. The ground field is complete
and ultrametric. The extension field is complete, algebraically closed and
ultrametric, with a normed algebra structure over the ground field. The final
strong statement specializes the chart-index universe to the space universe,
as required by the existing analytic étale site. No Hausdorff or nontrivial
valuation hypothesis is introduced.

The provenance is internal deduction from the finite-character lift, fixed
target chart extension, the existing canonical recognition quasi-isomorphisms
and their field-point bijections, and the published all-pieces étale
quasifiniteness theorem. This module does not prove domain residue comparison,
localized étale right cancellation, geometric refinement or equalization,
or the unconditional geometric-point theorem.
