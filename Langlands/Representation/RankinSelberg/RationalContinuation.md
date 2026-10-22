# Rational continuation in the local spectral variable

Author: Worker 11.

This pair supplies an intrinsic uniqueness argument for the rational
continuations used in JPSS local zeta integrals. It imports only the pinned
Mathlib environment. It does not prove convergence or existence of a rational
continuation of any integral.

For any field, `rationalFunction_eq_of_infinite_eval_eq` states and proves
that two rational functions agreeing at infinitely many points, where both
reduced denominators are nonzero, are equal. Evaluation is Mathlib's
`RatFunc.eval`. The proof cross-multiplies the evaluated numerators and
denominators. Two polynomials with equal evaluations on an infinite set
are equal; their equality then gives equality of the two fractions in the
fraction field. The theorem does not need an algebraically closed field.

For a natural number `q`, `spectralPoint q s` is the complex power `q^(-s)`.
`HasRationalContinuation q f R` means that there is a real bound beyond which
`f(s)` agrees with evaluation of the actual rational function `R` at that
spectral point, and that the reduced denominator of `R` is nonzero throughout
this right half-plane. Requiring denominator nonvanishing avoids interpreting
Lean's totalized division at a pole as analytic continuation.

When `q > 1`, real spectral parameters give the positive real powers
`q^(-t)`, embedded in the complex numbers. Strict monotonicity of real powers
makes this map injective. Every real right half-line is infinite, so its image
under the spectral map is infinite. The uniqueness proof takes the maximum
of the two continuation thresholds, applies the generic rational-function
lemma on this common half-line, and concludes equality. The final
`existsUnique_rationalContinuation` lemma packages an existing witness
together with this proved uniqueness. It assumes existence explicitly and
does not choose a rational factor.

The motivating original is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 2.4 and Theorem 2.7(i)–(ii), printed pages 387 and 390–391.
Registered source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those passages give convergence for sufficiently large real part and
rationality in `q^(-s)`. The algebraic uniqueness argument in this Lean file
is derived infrastructure, not a separately numbered theorem attributed to
that article. It applies to arbitrary functions before specializing to the
project's actual coefficient-model integrals.

This is development work until independent review and publication.
