# Proof of relative smoothness and flatness over the original rings

`ringSystemRelativeSmoothFlatDescent` proves exactly
`Langlands.AlgebraicGeometry.SchemeLimitModel.RingSystemRelativeSmoothFlatDescent`.
The statement's paired Markdown gives its source and all hypotheses.
Every construction works in arbitrary universe `u`.

The private `spectrumRelativePropertyDescent` specializes a proved relative
property equivalence to the actual spectrum diagram, structure maps and
cone of the supplied algebra diagram. `spectrumConeIsLimit` constructs the
limit witness from the algebra-colimit witness, and `spectrumCone_compat`
supplies the compatibility equations. Taking `unop` or `op` reindexes the
existential stage to the original algebra category.

The private `initialRingRelativePropertyDescent` applies the spectrum
result to `initialRingAlgebraDiagram` and `initialRingAlgebraCocone`.
Their colimit witness follows from finality of the actual under-category
tail and the ring/algebra equivalence. Their spectrum structure maps are
definitionally the original transition maps and cocone map, so the
conclusion concerns precisely the prescribed initial ring system.

The private `finitePresentationInitialRingRelativePropertyDescent` rewrites
the composite `f.left ≫ Y.hom` as `X.hom`. It then uses the published
`Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp` from
`Langlands.AbelianScheme.TorsionFiniteEtale`: local finite presentation of
the composite and local finite type of `Y.hom` imply local finite
presentation of `f.left`. `QuasiCompact.of_comp` and
`QuasiSeparated.of_comp` derive the other relative hypotheses from the
model hypotheses. The initial-ring property equivalence now applies.

The three public intermediate theorems instantiate these helpers for
smoothness and flatness using the proved `relativeSmoothDescent` and
`relativeFlatDescent`. The final theorem conjoins the spectrum,
initial-stage and finite-presentation forms. No affine or separated
model assumption and no injectivity of transition maps enter the proof.
