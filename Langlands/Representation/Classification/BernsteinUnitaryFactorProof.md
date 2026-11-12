# Unitarity of Hermitian factors of an irreducible unitary product

The theorem proves the unchanged published proposition
`Langlands.Classification.BernsteinUnitaryProductFactorUnitarity` for
independent field and coefficient-space universes. It is the finite-family
weak form of Tadic's Theorem 2.5(ii) specified by that proposition.
The proof uses the compact-picture route described below.

If the total rank is zero, the positive block sizes imply there are no
blocks, so the conclusion is vacuous. For positive rank, symmetrize each
supplied nonzero invariant sesquilinear form to obtain a nonzero invariant
Hermitian form. Their finite tensor form is nonzero, Hermitian and invariant
under the actual block Levi action.

The positive square root in normalized induction makes this coefficient
form transform by the full real block modulus. The published scalar
compact integral theorem supplies a compact open subgroup, a Haar
probability measure, integrability of every actual scalar pairing, and
right-translation invariance. Integrating therefore gives an invariant
Hermitian form on the actual smooth induction. Compact double-coset
sections show that this integrated form is nonzero.

Irreducible smooth general linear representations are admissible by the
published cuspidal embedding theorem. Scalar comparison with the given
invariant positive form makes the integrated form a nonzero complex
multiple of that positive form. Evaluate on a nonzero diagonal and use
Hermitian symmetry to show that the multiplier is real. Divide the
coefficient tensor form by this multiplier. Its integral is now exactly
the chosen positive form.

The compact positivity reflection construction then gives a positive
definite core on the entire coefficient tensor space. Levi invariance
is retained by the scalar division, so the actual external tensor
representation is unitarizable. For each block, insert a variable vector
in that coordinate of a fixed nonzero pure tensor. This is a nonzero
intertwiner into the restriction of the external tensor action.
Irreducibility of the block makes it injective; restriction and pullback
of the positive form prove that block is unitarizable.

The algebraic and compact integration prerequisites are separate paired
modules. Scalar comparison is supplied by
`Langlands.invariantSesquilinearScalar`. No positivity of the original
factor forms, additional finite-dimensionality, or equality of the two
universes is assumed.
