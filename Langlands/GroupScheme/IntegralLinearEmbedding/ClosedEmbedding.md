# Closed linear embeddings over principal ideal domains

This internal construction combines the finite-subcomodule
construction in `IntegralLinearEmbedding.FiniteSubcomodule` with the published
coordinate representation and affine corepresentation APIs. It addresses the
PID and DVR cases used by the reductive-monomorphism reduction; it does not
assert the corresponding result over every Dedekind domain.

All rings, algebras and schemes lie in an arbitrary universe `u`.
`ClosedEmbedding G` records a natural number `rank`, an actual homomorphism
`representation : MatrixRepresentation G (Fin rank)`, and the assertion that
its underlying scheme morphism is a closed immersion.

For a group-valued functor corepresented by a flat finite-type algebra over a
principal ideal domain, `exists_corepresented_closedEmbedding` supplies such
an embedding of the actual corepresented group scheme. Equip the algebra with
the published coordinate bialgebra and choose a finite set of algebra
generators. The finite-subcomodule matrix theorem gives finitely many matrix
coefficients spanning this set, with the comultiplication and counit identities.
These coefficients therefore generate the algebra. The published `toGLHom`
constructs the representation and `isClosedSubgroup_toGLHom` makes it a closed
immersion, by surjectivity of the coordinate-ring map.

`flat_of_iso` transfers flatness of a structure morphism through an isomorphism
over the affine base and uses the affine scheme criterion to recover module
flatness of the coordinate algebra. `exists_closedEmbedding` chooses an affine
coordinate presentation of an actual group scheme, uses the published
`AffineCorepresentation.finiteType_of_iso` and this flatness transfer, and
applies the corepresented construction. The inverse of the published comparison
isomorphism is an actual group-scheme homomorphism, so composition transports
the closed embedding back to the specified group scheme.

`closedEmbedding G` chooses one resulting embedding; no canonical choice is
claimed. `closedEmbedding_isClosedSubgroup` exposes its closed-immersion
property. `exists_isClosedSubgroup_of_pid` gives the existential form for any
flat affine group scheme with locally finite-type structure morphism over a
PID. `exists_isClosedSubgroup_of_dvr` specializes it to a DVR. Neither result
assumes smoothness, reductivity or separation by ring-valued linear
functionals. No additional axiom or embedding premise is introduced.

The finite-subcomodule input follows Milne's 2012 notes, VIII Aside 4.7, as
documented in its own paired Markdown. The present module is an internal
composition of that result with published coordinate and affine-transport
constructions; it makes no new direct attribution to the literature.
