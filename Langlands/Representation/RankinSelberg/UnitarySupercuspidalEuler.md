# Certified unitary supercuspidal Euler factors

This internal adapter uses the exact finite datum
`UnitaryContragredientTwistParameterSet F π σ` of two supplied equal positive
rank representations at independent field and two carrier universes. Its
`eulerData` has the actual residue cardinality as spectral base and exactly
those twist parameters. Its parameter set contains one precisely when the
first representation is equivalent to the smooth contragredient of the second.

The theorem `isPadicPairLPolynomial` takes the explicit premise
`SupercuspidalEqualRankLFactorStatement`. Given its irreducibility,
supercuspidality and Whittaker-type inputs, it identifies the formula's finite
set with the supplied exact twist set by their membership predicates. This
certifies the actual finite Euler polynomial. The equal-rank factor formula is
not proved in this module.

Given certification of that polynomial, uniqueness identifies the reciprocal
of every other certified polynomial evaluated at the actual JPSS spectral
point with `eulerData.reciprocal`. The equality is pointwise, including the
totalized reciprocal values at Euler zeros; the analytic conclusions use
meromorphic orders and punctured germs. The final theorem proves meromorphy
and finite nonpositive order at every complex point, analyticity and nonzero
value off the imaginary axis, and strictly negative order at zero for an
actual contragredient pair.

The provenance is internal composition of the exact twist-set construction,
the published conditional JPSS formula interface and polynomial uniqueness,
the equality between the complex-power and exponential spectral conventions,
and the finite unitary Euler analysis. No L-factor formula, unequal-rank
identification, segment formula, or associated-pair induction theorem is
claimed without its retained premises.
