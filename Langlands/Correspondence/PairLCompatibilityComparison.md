# Comparing compatible pair L-polynomials

Author: Worker 422.

This supporting helper module is derived from the existing
`IsPairLCompatibleAt` definition. It is intended for the rank induction in
`AssemblyLCharacterizationStatement`; it does not prove that statement or any
assembly, classification, or inheritance prerequisite. The field, parameter,
and automorphic carrier universes remain independent.

`IsPairLCompatibleAt.common_polynomial` compares two supplied compatibility
certificates with the same parameter pair and additive character. For any
supplied self-dual measure, each certificate yields a polynomial whose inverse
in `RatFunc ℂ` equals the same arithmetic pair L-factor. Injectivity of inversion
and of the polynomial algebra map into rational functions makes the two
polynomials equal. Transport along that equality gives one polynomial certified
for both pairs of automorphic classes.

`IsPairLCompatibleAt.same_pole_order` uses that common polynomial twice. Its two
pole orders, defined by the existing representation-side statement as the root
multiplicity at one, are therefore equal by reflexivity. The comparison makes no
nonvanishing assumption: inversion is injective on the whole field, including
zero. The certified-polynomial relations separately supply their own usual
normalization.

These are internal logical consequences of the published factor interfaces.
They implement the equal-L-factor step in Henniart 2002, section 4.5, printed
page 600 (registered source `henniart-2002-characterization`), without claiming
the subsequent use of the square-integrable characterization or its proof.
