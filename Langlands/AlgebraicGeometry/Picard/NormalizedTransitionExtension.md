# Extension from normalized generic frame transitions

This internal construction uses an arbitrary valuation domain `R`, the
supplied fraction field `K`, a smooth geometrically connected morphism
`p : X ⟶ Spec R`, and an actual pullback square with projection
`q : Y ⟶ X` and structure map `s : Y ⟶ Spec K`. It builds on
`GenericFrameNormalization` and `GenericTransitionExtension`.

`GenericScalarNormalization.transitionUnit` takes normalization data
`n` for a generic overlap-unit cocycle `g`. For indices `i,j`, assume
that `T i ∩ T j` and `W = (T i ∩ T j) ∩ T i₀` are affine,
that `W` meets the closed fibre, and that the actual section algebra on
`T i ∩ T j` is projective over `R`, with the algebra structure
`affineSectionAlgebra p`. The construction returns an actual unit on
`T i ∩ T j` whose image under the original `q.app` is the changed
transition `n.scalar i * g i j * (n.scalar j)⁻¹`, after restricting
the scalar factors.

The implementation restricts the changed transition to `W`.
The normalization restriction theorem identifies it with the pullback
of `(n.totalUnit i|W)⁻¹ * (n.totalUnit j|W)`.
`affineGenericUnitOfRestriction` then lifts this generic unit to the
larger total overlap. Equality is retained as an equality of units
under the actual section map. Projectivity is required on the larger
overlap algebra; it is not assumed on the triple intersection here.

`exists_lineBundle_of_normalized_frames` applies this construction to
the canonical cocycle of actual local frames of a given line bundle
`D` on `Y`. In addition to normalization, it assumes that the total
opens cover `X`, that `q.app U` is injective for every total open `U`,
and that the above affineness, closed-fibre intersection, and
projectivity hypotheses hold for every pair of indices.
It concludes that an actual total line bundle `E` exists with an actual
module-sheaf pullback isomorphism `q* E.obj ≅ D.obj`.

The proof changes the original frames by the inverses of the scalar
units and uses `frameCocycle_unitGaugeFrames` to identify their canonical
transitions. The chosen total units lift these transitions. The imported
`exists_lineBundle_of_frameCocycle_lifts` reflects the cocycle identity
using sectionwise injectivity and glues the total line bundle.
No compatibility among independently chosen total lifts is an input.

`lineBundleOfNormalizedFrames` chooses the resulting actual total bundle.
`normalizedFramesIso` chooses its actual module-sheaf isomorphism under
the original morphism `q`. The scalar changes are changes of frame in
the given generic bundle, so the isomorphism has target `D.obj` itself.

The provenance is internal: the proof composes the imported normalization,
unit-detection, frame-change, and gluing interfaces as described above.
This module does not establish geometric projectivity, construct the
normalization inputs for an arbitrary cover, or prove the unconditional
two-axis extension statement.
