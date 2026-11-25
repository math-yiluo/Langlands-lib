# Global identity coherence of determinant pullback

This module is derived from the Library's determinant frame construction and
its local generator formulas. It supplies the identity law for the actual
pullback comparison of determinant sheaves and lifts that law to actual line
bundles. It works in every universe `u`, for a module sheaf `M` on a scheme `X`,
a covering family `T : ι → X.Opens`, and free frames indexed by a finite type
`I`. The frame rank is constant in this module.

`pullbackIso_eq_of_generator_image` compares the composite of the determinant
pullback comparison with a supplied isomorphism `b` against another supplied
isomorphism `c` into an arbitrary module sheaf. Its hypothesis compares their
images of every local determinant generator after pullback. The proof uses the
published generator formula for `pullbackIso` and extensionality on pulled-back
generators, proved by sheaf separation and pullback adjunction in the imported
coherence module.

`pullbackIdentityIso_generator_image` shows that the determinant map induced by
the module identity-pullback comparison sends the generator of each pulled-back
frame to the original generator. It applies the imported generator formula on
the identity-preimage open, then identifies that open with the original open.

`pullbackIsoIdentityStatement` is the equality between the composite
`pullbackIso e (𝟙 X) hT ≪≫ pullbackIdentityIso e hT` and the canonical module
pullback identity comparison. `pullbackIso_identity` proves this equality by
the comparison criterion: the first comparison returns each original generator,
and the module pullback identity returns each original section.

`lineBundlePullbackIdentityIso` is the actual isomorphism from the determinant
line of the identity-pulled-back frames to the original determinant line. Its
underlying map is `pullbackIdentityIso`. `lineBundlePullbackIso_identity` proves
that composing it with `lineBundlePullbackIso e (𝟙 X) hT` gives the canonical
identity comparison in the category of line bundles. The proof forgets to
module sheaves and applies the preceding identity law.

The construction and proofs are internal consequences of the cited Library
APIs. This module supplies the identity law; composition is proved in
`DeterminantComposition`, naturality and variable rank are treated in
`DeterminantVariableNaturality` and `DeterminantVariableCoherence`, and the
parabolic polarization construction is not part of this module.
