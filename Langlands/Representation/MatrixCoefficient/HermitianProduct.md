# Hermitian products of matrix coefficients on the central quotient

Worker 577 constructs `Langlands.UnitaryCentralCharacter.coefficientProduct`.
For an actual representation `rho`, a prescribed actual unitary central character
`c`, an algebraic functional `ell`, and vectors `u`, `v`, this is a complex function
on the actual quotient `G / Z(G)`. Its value at the class of `g` is
`conjugate(ell(rho(g)u)) * ell(rho(g)v)`. The group and carrier have independent
universes. The carrier is an arbitrary complex module; no topology, norm,
dimension condition, or positive form on it is used.

## Construction and algebraic laws

`matrixCoefficientProduct_mul_center` derives central invariance from the
published `matrixCoefficient_mul_center`. Both coefficients acquire the same
scalar `c.character z`; their product acquires its conjugate times itself.
The character's unit norm makes this factor one. `coefficientProduct` uses
`Quotient.lift` with this invariance, and `coefficientProduct_mk` gives the
representative formula.

`norm_coefficientProduct` identifies its norm with the product of the two
published `coefficientNorm` functions. `coefficientProduct_conj` gives conjugate
symmetry, and `coefficientProduct_self` identifies the diagonal value with the
real square of `coefficientNorm`, coerced to the complex numbers.
The `zero_left`, `zero_right`, `add_left`, `add_right`, `smul_left`,
and `smul_right` lemmas give the usual sesquilinear laws, pointwise on the
quotient: conjugate-linearity in the first vector and linearity in the second.
`coefficientProduct_translate` states that applying `rho h` to both vectors is
right translation of the quotient argument by the class of `h`.
`coefficientProduct_eq` proves independence from the chosen central-character
datum. These laws reduce to representatives and use the corresponding
algebraic laws of the actual coefficients.

## Regularity

For a topological group and two smooth vectors,
`continuous_coefficientProduct` applies the quotient-map criterion for
`G → G / Z(G)`. The pullback is a product of the conjugate of one coefficient
and the other coefficient. Each coefficient is locally constant by the
published `matrixCoefficient_isLocallyConstant`, which needs only the
smoothness of its vector, with no smoothness requirement on the functional.
Continuity of conjugation and multiplication proves continuity of the pullback.

For a Borel measurable structure on the quotient,
`measurable_coefficientProduct` gives Borel measurability, and
`aestronglyMeasurable_coefficientProduct` gives almost everywhere strong
measurability for every measure on that quotient. The latter follows from
continuity and the second-countable complex codomain. No Haar, finiteness,
sigma-finiteness, or integrability assumption is used.

## Internal provenance and scope

This is an internally derived construction from the published actual central
character and matrix-coefficient interfaces, together with Mathlib's complex
conjugation, quotient topology, and continuity/measurability APIs. It does not
claim to reproduce an external definition verbatim. It supplies the
conjugate-first integrand for the integral-form route motivated by Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups*, May 1, 1995, Proposition 2.5.4, printed/PDF pages 28–29.
The parent target records literature ID
`casselman-1995-admissible-representations` and retained SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The original is retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Pages 28–29 were read, and the displayed formula on page 29 was also checked
in the rendered original. No source-specific project errata note was found.
Casselman's displayed form conjugates the second factor. The conjugate-first
convention here reverses the source form's arguments, preserves its diagonal,
and agrees with `InnerProductSpace.Core`.

Direct project imports are `MatrixCoefficient.ModuloCenter` and
`MatrixCoefficient.LawsProof`; no existing pair is changed. This pair proves
only the descended function and its construction laws. Integrability,
integration to a positive form, and construction of a unitary realization
remain separate proof obligations.
