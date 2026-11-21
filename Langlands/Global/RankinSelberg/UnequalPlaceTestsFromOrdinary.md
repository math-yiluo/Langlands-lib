# Dual unequal-rank test nonvanishing from the local functional equation

`unequalPlaceTestsFromOrdinary` proves `UnequalPlaceTestsFromOrdinaryStatement`. At either field, the corresponding local unequal-rank functional equation and the ordinary test existence input imply the place-test assertion for that field. The real and complex deductions are independent.

`RealUnequalOrdinaryPlaceTestsStatement` and `ComplexUnequalOrdinaryPlaceTestsStatement` are open inputs. At the specified place of the number field, with the two original cuspidal realizations and the additive component, they ask for actual restrictions of opposite-character Whittaker coefficients and compatible quotient measure data in the smaller rank. For this one fixed pair and measure the ordinary integral must be nonzero somewhere in every right half-plane. No choice of a contragredient or statement about the dual integral is required for this ordinary input.

## Implemented proof

1. Apply the local functional-equation premise to the pair chosen by the ordinary input. Its convergence half-plane supports both holomorphic integrals and their agreement with the supplied continuations. Choose an ordinary nonzero point in that half-plane. The ordinary continuation is analytic there by agreement with the ordinary integral, so the meromorphic identity principle gives ordinary nonvanishing along the codiscrete filter on `ℂ`.
2. The multiplier on the right of the multiplied-out functional equation is nonzero off a discrete set. The epsilon factor takes values in complex units. The reflected dual L-denominator is a nonzero entire function after composition with `s ↦ 1 - s`, hence is nonzero off a discrete set. If `-1` acts by a scalar, that scalar is nonzero because its action on the nonzero cuspidal carrier is invertible; the fallback scalar is one.
3. In a punctured neighborhood inside the open set `σ < Re (1 - s)`, choose a point where the equation holds and both the ordinary continuation and its multiplier are nonzero. The equation forces the dual continuation at `1 - s` to be nonzero. This is a point of the dual integral's convergence half-plane, so the same pair and measure give the required dual nonzero value. This argument does not require a claim about individual values at any exceptional point and never divides by the ordinary L-factor.

## Fixed-place form

`hasRealUnequalPlaceTest_of_ordinary` and `hasComplexUnequalPlaceTest_of_ordinary` carry out the argument above at one place. They take the corresponding closed local functional equation, the data of that equation at the given place, and one supplied actual pair with quotient measure data whose ordinary integral is nonzero arbitrarily far to the right. The conclusion is `HasRealUnequalPlaceTest` or `HasComplexUnequalPlaceTest` for the same pair and measure. The closed implications `realUnequalPlaceTests_of_ordinary` and `complexUnequalPlaceTests_of_ordinary` choose the pair from the ordinary input and apply these lemmas. The fixed-place lemmas let other constructions of an ordinary pair, for example from local normalized generation, reach the place tests without the closed ordinary assertion.

## From a normalized ordinary test

`OrdinaryIntegralNormalization.exists_ne_zero_above` proves that a single supplied normalized test with nonzero entire value at one point gives ordinary nonzero values arbitrarily far to the right. In the half-plane where the ordinary integral agrees with the entire normalization times the reciprocal L-denominator, choose a point avoiding the discrete zero sets of the normalization and the denominator. This can be applied to a test from model-side normalized generation once the test is identified with actual restrictions. It does not construct the model-side test or that identification.

## Scope and provenance

This is an internal consequence of the Library's multiplied-out local equation, based on Jacquet 2009, Theorem 2.1(iii), and the ordinary test route of Theorems 2.3 and 2.6(i), for the pointwise step of Cogdell 2004, proof of Theorem 4.1, p. 219. The named functional equations, ordinary test existence and actual-model transport needed for that existence are not proved here. The result is not an unconditional proof of either place-test assertion or the pointwise target.
