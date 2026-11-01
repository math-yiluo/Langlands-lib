# Scalar test coordinates and the Tate functional equation

This module is an internal derivation from the published independent equal-rank
Rankin–Selberg functional equation. Its final theorem specializes that result to
the actual scalar character representation on GL(1) paired with the trivial
representation. It retains the canonical normalized absolute value, canonical
multiplicative Haar measure, and the supplied additive Haar measure. It does not
assume a scalar functional equation or construct the full matrix analytic datum.

The coordinate definitions `tateRowScalarHomeomorph`, `tateRowTest`, and
`tateScalarRowTest` identify a one-coordinate row with its scalar entry. They
preserve Schwartz–Bruhat tests through homeomorphic pullback. The inverse
transport after `tateRowTest` is the identity. `tateCharacterFunctional` is the
identity linear form on the scalar character representation; in rank one the
unipotent group is trivial, so this is an actual Whittaker functional and is
nonzero. `tateCharacterModel_apply` proves that every coefficient in its image is
its value at the identity times the character of the determinant, by lifting it
through the actual model map.

`rowFourierIntegral_tateRowTest` proves equality of the row Fourier integral and
the scalar plus-sign Fourier integral. The proof uses the measure-preserving
unique-coordinate equivalence for the product of one copy of the supplied
additive measure. `tateScalarFourierPair_of_row` then transports an actual row
Fourier witness to a scalar Schwartz–Bruhat witness, including integrability at
every Fourier parameter. Neither assertion replaces the given measure by a
rescaled or separately chosen measure.

In the canonical p-adic topology, `tateEqualRankIntegral_eq_scalar` identifies the
original rank-one model integral with the weight-one scalar Mellin integral.
The product of the two coefficient values at the identity is absorbed into the
scalar test. The quotient integral is transported first to the actual GL(1)
Haar integral by the published rank-one quotient result, then to the scalar
multiplicative Haar integral by `integral_tateScalarEquiv`.
`tateDualEqualRankIntegral_eq_scalar` follows the same route for the actual dual
functions. The rank-one long Weyl matrix is the identity, and the determinant of
the inverse transpose is the inverse determinant. Thus the dual scalar
coefficient is the complex-valued inverse character, with the same product of
coefficient values at the identity. These are integral equalities for every
complex parameter; they do not invoke rational continuation.

The two model-map images of the scalar unit both have value one at the identity.
The two `unit_eq_scalar` theorems consequently remove the coefficient multiplier.
`tateEqualRankRationalValues_eq_scalar` and
`tateDualEqualRankRationalValues_eq_scalar` prove equality of the complete
rational-value families. In one direction all vector coordinates are absorbed
into a scalar test; in the other direction the unit model vectors and the row
pullback realize every scalar test. The equalities concern all actual rational
continuations, rather than chosen generators or a larger comparison family.

The final theorem `Padic.tateScalarFunctionalEquation` fixes a continuous
quasicharacter, an additive character, its supplied self-dual additive Haar
measure, and normalized-generator certificates for the scalar character and
inverse-character Mellin families at weight one. It returns a nonzero complex
constant and an integer exponent before all scalar tests. For every test it
returns an actual Schwartz–Bruhat Fourier transform, together with pointwise
Fourier integrability and the plus-sign integral identity. Every pair of
rational continuations of the original and transformed scalar Mellin integrals
satisfies `NormalizedFunctionalEquation` with those fixed generators and
constants, rank index zero, and the trivial sign scalar.

The implemented proof supplies the Whittaker hypotheses using
`rankOneCharacter_isOfWhittakerType`, converts the trivial character to inverse
standard Whittaker type, and applies the published
`equalRankFunctionalEquation` at rank index zero with the compatible rank-one
quotient Haar measure. Equality of rational-value families and
`IsNormalizedGenerator.unique` identify its two polynomials with the supplied
ones. The unit vectors and Fourier coordinate comparison give the scalar
witness. Uniqueness of rational continuation extends the resulting equation to
every continuation pair. Its sign exponent is zero, so the theorem's auxiliary
minus-one scalar disappears. No Whittaker hypothesis or analytic premise is
left beyond the stated scalar generator certificates and self-duality.

This is a derived construction, not a transcription of an additional literature
statement. Its analytic input is the already published independent equal-rank
theorem; its measure and Mellin definitions are imported by Lean name. The
matrix integral, full analytic datum, and transport back to an arbitrary
admissible irreducible GL(1) carrier are separate parts of the host Tate matrix
base proof.
