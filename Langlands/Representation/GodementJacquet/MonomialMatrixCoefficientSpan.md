# Extending a monomial matrix equation over the coefficient span

This internal algebraic construction extends an actual matrix functional
equation from smooth elementary matrix coefficients to their complex span.
Its provenance is the published definition of `biSmoothMatrixCoefficients`,
linearity of convergent matrix integrals and their actual rational values,
the complex algebra homomorphism for rational reflection, and uniqueness of
rational continuation for residue cardinality greater than one.

`normalizedFunctionalEquation_of_monomial_rational_identity` proves the
converse of the existing reflected rational identity for a monomial equation.
It evaluates the identity at `q^(-s)`. The two supplied denominator guards
justify evaluation of the original value and the reflected dual value.
The Laurent monomial is regular at every nonzero point and evaluates to
`c*q^(-ms)`. The resulting equation is exactly
`NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual`; both guards remain in
the conclusion.

For fixed full-matrix tests `Phi` and `PhiHat`, a nonzero complex reflection
parameter `delta`, and a fixed rational multiplier `M`,
`matrixMonomialCoefficientSubmodule` consists of coefficient functions having
actual shifted rational values at those tests whose rational functions obey
`subst(delta,RDual)=M*R`. It is a complex submodule. Zero has zero actual
values. Actual rational values add on a common right half-plane, and scalar
multiples preserve actual values, including the zero scalar. Reflection
preserves addition and complex scalars, so the fixed rational identity
survives both operations.

`matrixMonomialIdentity_of_biSmoothGenerators` uses the defining span of
smooth elementary coefficients to place every bi-smooth coefficient in this
submodule. Uniqueness identifies the resulting witnesses with any supplied
actual original and dual rational values. The theorem retains convergence
and continuation in each actual-value premise.

`normalizedFunctionalEquation_of_biSmoothGenerators` combines this extension
with both directions of the rational identity equivalence. The fixed unit
and integer exponent are unchanged throughout the coefficient span. The two
tests are fixed before the coefficients; no Fourier witness or measure is
chosen by this construction, and no analytic or supercuspidality conclusion
is asserted here.
