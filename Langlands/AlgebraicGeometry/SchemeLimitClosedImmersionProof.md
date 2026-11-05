# Proof of closed-immersion detection in affine scheme diagrams

Worker 105 authored this proof, reused here by Worker 1596.

`affineDiagramClosedImmersionDescent` proves the exact proposition
`Langlands.AlgebraicGeometry.AffineLimit.AffineDiagramClosedImmersionDescent`
in `SchemeLimitClosedImmersionStatement`. The source and derived scope
are documented in that statement's paired Markdown.

The implemented proof applies `Scheme.Γ` to the actual opposite scheme
diagrams and actual opposite limit cones. Mathlib's affine-limit
preservation constructs both ring-colimit witnesses. Applying
`Scheme.Hom.appTop` to the given cone equations proves compatibility of
the actual limiting ring map.

`HasRingHomProperty.appTop` obtains finite type at the chosen component.
`isPushout_appTop_of_isPullback` turns each given actual Cartesian square
into the ring pushout with the required orientation. The limiting closed
immersion has affine target by affine-limit preservation, so
`IsClosedImmersion.isAffine_surjective_of_isAffine` gives surjectivity of
its actual global-sections map.

The proof invokes `finiteTypeSurjectivityDescent` for these actual ring
diagrams, cocones and maps. It takes `unop` of the returned stage and arrow,
and applies `IsClosedImmersion.of_surjective_of_isAffine` to the returned
surjective component. No injectivity of transitions or finite presentation
is used. This proof retains the affine scope and remaining geometric
obligations recorded in the statement.
