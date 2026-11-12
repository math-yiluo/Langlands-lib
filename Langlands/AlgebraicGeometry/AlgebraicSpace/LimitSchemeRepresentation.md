# Scheme models and eventual scheme representation at affine limits

This is an internal supporting result for the algebraic-space limit descent
problem. It combines the published scheme model existence theorem with the
published formulation of essential uniqueness of algebraic-space models.
The uniqueness assertion is an explicit premise throughout the second result.

`schemeModelBaseChangeIso` constructs the comparison between the represented
top-left scheme of a cartesian square and the base change of its represented
top-right scheme. It combines the pullback isomorphism in the slice category
with the scheme-to-space base-change comparison.

`exists_schemeModel_of_affineLimit` is unconditional. A scheme over the limit
with locally finitely presented, quasi-compact, quasi-separated structure map
has a scheme model with the same three properties at an actual stage of any
cofiltered diagram of affine schemes. The result includes the actual cartesian
square, with the original limiting-cone projection as its bottom edge.

The proof applies global sections to the opposite limit cone to obtain a
filtered ring colimit. It applies `schemeFilteredModelExistence` to the given
structure map followed by the canonical affine spectrum isomorphism.
Naturality of that isomorphism converts the resulting spectrum square back to
the original affine scheme diagram.

`exists_schemeRepresentation_of_limit_of_modelUniqueness` assumes
`SpaceLimitModelUniqueness`, the original space's quasi-separatedness and
locally-finitely-presented quasi-compact atlas, and an actual isomorphism of
its limit base change with a scheme whose structure map has the same three
finiteness properties. It produces a later arrow to the original stage and a
scheme with these three properties representing the corresponding base change.

The proof first restricts to the cofinal category of arrows into the original
stage. The unconditional scheme result gives a scheme model in that category.
The cartesian square and iterated base-change comparison identify the limit
base changes of the space model and scheme model. Scheme finiteness supplies
the required atlas and quasi-separatedness of the latter. The supplied
essential-uniqueness premise gives an isomorphism at a later stage, and the
scheme base-change comparison gives the claimed scheme representation there.

These are derived categorical and scheme-model consequences of existing
interfaces. They do not prove `SpaceLimitModelUniqueness` or any of the remaining
unrestricted algebraic-space property descent assertions.
