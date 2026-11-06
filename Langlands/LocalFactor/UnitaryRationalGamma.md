# Unitary arithmetic gamma orders from the actual rational factor formula

This internal derived construction evaluates an actual rational function at the
published Rankin–Selberg spectral point. It transfers the unitary Euler order
bound to the actual rational expression in `IsArithmeticPairGammaFactor`.

The epsilon factor in that relation is already a nonzero Laurent monomial
`c X^m`. Its evaluation is analytic at every spectral parameter: the spectral
point is a nonvanishing exponential, and every integer power of that
exponential is analytic. This argument applies to the monomial provided by the
relation and needs no separate analyticity assumption on an arbitrary
local-constant assignment.

For an actual Weil–Deligne pair with unitary underlying action, the rational
L-ratio has the original Euler polynomial in its numerator and the reflected
dual Euler polynomial in its denominator. The proof uses the existing
`rationalLRatio_eq` and Rankin–Selberg rational evaluation theorem. The
reciprocal change of variable agrees exactly with `s ↦ 1-s`. The reflected
denominator is an entire function which is nonzero at zero, by the unitary
Euler estimate for the dual at one. Its zeros are isolated, so this rational
evaluation agrees with the existing determinant gamma expression throughout a
sufficiently small punctured neighborhood of every complex point.

Equality of these punctured germs preserves meromorphic order, including at
poles and at singularities removed by rational cancellation. The existing
`spectralGammaExpression_order_nonpos` then proves nonpositive order whenever
the real part of the parameter is nonzero. Both the actual pair and its dual,
their monodromy kernels, the supplied normal subgroup and the acting group
element are retained. Group and carrier universes are independent.

The correspondence corollary extracts the constant and integer exponent from
the original `IsArithmeticPairGammaFactor` relation. For any two actual local
pairs with unitary underlying actions, it applies the bound to their actual
tensor. The field universe, local carrier universe and local-constant-system
carrier universe remain independent. The local subgroup, geometric Frobenius,
canonical residue cardinality and original rational function are unchanged.

The final two corollaries specialize this result to the actual local pair
classes of a unitary relative Weil representation `S` and its contragredient.
They obtain the required local unitarity by restriction of the original
positive form and published dual unitarity. On the real axis, a positive order
of this actual rational factor can therefore occur only at zero. These
corollaries retain the supplied local map and gamma relation; they do not
construct either datum or assert its global compatibility.

The provenance is algebraic rational evaluation and elementary complex
analysis applied to the already published local-factor constructions. No
additional original-source assertion is used. This result does not construct
an arithmetic gamma factor, prove any supplied-pair gamma comparison, or prove
the associated-pair induction statement. The all-intermediate-field
analyticity theorem for arbitrary supplied local-constant systems remains a
separate obligation.

Author: Worker 1768.
