# Smooth Hopf coordinates and scalar extension

This internal adapter supplies algebraic hypotheses for the arbitrary-field
commutative p-torsion embedding proof. It does not prove primitive generation
or construct the embedding.

Let `R` be any commutative ring in universe `u`, and let `G` be an actual group
scheme over `Spec R` with affine underlying scheme and smooth structure
morphism. Its chosen Hopf algebra `AffineCoordinates.hopfAlgebra G` has exactly
the underlying algebra `AffineCoordinates.algebra G`.

`hopfAlgebraSmooth` installs smoothness of that Hopf coordinate algebra. It
applies the published `AffineCoordinates.smooth_algebra`, whose proof
transports smoothness through the actual affine corepresentation isomorphism.

For any commutative `R`-algebra `B` in an independent universe `v`,
`hopfAlgebraBaseChange_smooth` gives smoothness of
`B ⊗[R] hopfAlgebra G` over `B` by Mathlib's `Algebra.Smooth.baseChange`.
`hopfAlgebraBaseChange_finiteType` follows from smoothness, which includes
finite presentation and hence finite type.

If `B` is a domain, `hopfAlgebraBaseChangeReduced` installs reducedness of that
tensor product. It applies the published ring theorem
`SmoothReducedProof.isReduced_of_smooth_of_domain` over `B`.
In particular, these constructors give finite type and reducedness after
extension from any field `k` to any extension field, including an algebraic
closure. No characteristic, commutativity of the group, connectedness,
perfectness, or infinitude hypothesis is used.

The two instance constructors are marked `instance_reducible`, matching the
existing `AffineCoordinates.algebraFiniteType` interface. The intermediate
smoothness and finite-type results are named for explicit use, while those
properties already follow through Mathlib's instances.

The provenance is internal: this is a composition of the published coordinate
smoothness theorem, Mathlib's scalar-extension and finite-presentation
instances, and the published reducedness theorem. It makes no additional
claim about the original-source group classification.
