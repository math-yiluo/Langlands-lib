# Exact normalization of tail polynomials at compact generators

This internal algebraic construction identifies the normalized tail polynomial
at `-i` times a compact generator with the monic central-factorial sequence
of `RealCompactPolynomialRelations`. Write `P_n` for the tail polynomial
and `D_n(X)=factor X n`, where `D_0=1`, `D_1=X` and
`D_(n+2)=(X²+(n+1)²)D_n`.

For every complex associative unital algebra and every element `X`,
`operator_normalization` proves the exact equality

`2^n n! P_n(-i X)=(-i)^n D_n(X)`.

No commutativity or nonzero-divisor condition on the algebra is assumed.
The helper `operator_eq_factor` divides only by the nonzero complex scalar
`2^n n!`, giving the corresponding explicit scalar multiple of `D_n(X)`.

The proof first establishes the two-step scalar recurrence

`4(n+1)(n+2) P_(n+2)(z)=(z²-(n+1)²)P_n(z)`.

This follows from one left and one right falling-factorial recurrence,
together with the factorial denominator. Two-step induction after setting
`z=-iX` proves the normalized equality for complex scalar arguments.
The cases zero and one are computed directly.

Polynomial extensionality lifts the scalar equality to the complex
polynomial ring. Evaluation in any complex algebra then proves the
operator equality. The auxiliary `aeval_factor` verifies that the defining
recursion of `factor` commutes with polynomial evaluation. This last step
requires no commutation between different algebra elements.

`RealTailCompactPolynomialNormalizationStatement` asserts the universal
operator normalization, and `realTailCompactPolynomialNormalization`
proves it. This provides the exact scalar comparison needed when applying
compact polynomial identities to differential-sign Fourier multipliers.
It asserts no equality of actual crossing words or filtration kernel images.
