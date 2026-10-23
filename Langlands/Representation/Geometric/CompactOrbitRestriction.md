# Compact restriction to a relatively closed orbit

This internal construction upgrades the published smooth orbit restriction to
compact induction. It takes an actual homeomorphism from the stabilizer's
left quotient to the coset orbit, together with its representative formula
`[q] -> [w^-1 q]`. Construction of that homeomorphism is a separate obligation.

For an actual compactly induced function `f` whose projected support lies in
`U`, assume that the coset orbit is closed relative to `U`. The support of the
restricted function is exactly the inverse image of the ambient projected
support under the supplied homeomorphism followed by the orbit inclusion.
The proof checks this equality on quotient representatives using the existing
covariance-based saturation of nonzero support.

The ambient support is compact. Lift it to `U`, intersect with the relatively
closed orbit, and map back to obtain a compact intersection in the ambient
quotient. Its lift to the orbit is compact, as is its inverse image under the
homeomorphism. This proves compactness of the restricted function's projected
support. `compactOrbitRestriction` pairs this proof with the existing smooth
restriction and preserves the evaluation formula definitionally.

For invariant `U`, `supportOrbitRestrictionNat` bundles this map as a natural
transformation from the existing smooth-input support subfunctor to the
existing compact orbit-piece functor. Pointwise linearity is definitional,
associativity proves equivariance under `Q`, and postcomposition proves
naturality. For an `OrderedDoubleCosets`, `supportStepOrbitRestriction`
specializes it to the next initial union using the published relative
closedness lemma. `supportStepOrbitRestriction_kernel` applies the published
pointwise lower-support criterion to identify its kernel with precisely
`lowerInUpper` of the preceding and upper support steps.

No openness of `U`, containment of the whole orbit in `U`, local compactness,
or closedness of the subgroups is needed once the actual homeomorphism is
supplied. The coefficient ring, group, and representation carrier have
independent universes; the inducing representation can be arbitrary.
This conditional construction proves neither the homeomorphism nor section
extension, surjectivity, or the full Mackey filtration theorem. Its provenance
is the elementary topology of compact sets and relatively closed subspaces,
applied to the existing concrete induction definitions.

Author: Worker 112.
