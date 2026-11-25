# Finite adelic factors and archimedean multiplicity spaces

This internal construction for the cuspidal contragredient of dual cusp forms
(`CuspidalTransposeInverseContragredientStatement`) separates the finite adelic action
from the compact and genuine enveloping actions on an actual operator
realization `S`. Its inputs are the existing concrete operators, the
published full-operator generator stability theorem, Jacobson density and
admissible Schur. It does not assert an all-place restricted tensor
presentation or construct any invariant pairing.

For an actual finite subrepresentation `A` of `S`, the multiplicity space
is the space of finite-equivariant maps from `A` to `S`. The compact
representation and enveloping algebra act on this space by postcomposition.
Finite/compact and finite/enveloping commutation ensure that these maps
remain finite-equivariant. Evaluation sends `a ⊗ f` to `f a`. Its three
covariance formulas place the finite action on `A` and the compact and
enveloping actions on the multiplicity space.

When `S` is irreducible for the full concrete operator algebra and `A` is
nonzero, evaluation is surjective. Its range is stable under all three
generator families and contains every vector of `A`, using its inclusion
as a multiplicity map. Full-operator irreducibility makes this range all
of `S`.

If the finite representation on `A` is irreducible and admissible,
evaluation is also injective. To reuse the published density argument
`TwoFactorExistence.eval_injective`, the proof extends the finite
representation to its product with the trivial group. That density
argument requires irreducibility and scalar endomorphisms of `A`; it
does not require irreducibility for the extended product action.
Admissible Schur supplies the scalar endomorphisms. Thus the tensor
evaluation is a complex-linear equivalence onto the actual carrier of `S`.
