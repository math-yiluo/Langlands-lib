# Regularity of the Section 4.7 lower integrand

This is a derived regularity result for the actual objects in
`TwoBlockLowerUnfoldingIntegrandData`. It supplies the measurability part of the
fixed-slice convergence argument. It asserts no outer integrability or growth
estimate.

The first-block partial Fourier value is locally constant in the group element:
the published row smoothness theorem makes the entire translated row function
locally constant, and postcomposition by its fixed Fourier integral preserves
local constancy. The character, plus sign, first coordinate, second-block row
and supplied additive Haar measure remain exactly those of `partialSection`.
This argument does not require a topological vector space of test functions.

Evaluation of a smooth opposite-parabolic section is locally constant because
the whole section has an open right stabilizer. Contracting its tensor values
by the fixed block functionals preserves local constancy. The same principle,
applied to the smooth coefficient model and evaluation at the identity, gives
local constancy of the actual test coefficient function.

Multiplication of the three factors gives local constancy of `groupIntegrand`.
The existing representative formula and the quotient topology then give local
constancy of `integrand` on the actual lower quotient. Thus it is continuous
and measurable for the canonical topology and any matching Borel measurable
structure.

`continuousIntegrand` bundles this same function with its continuity proof;
`continuousIntegrand_apply` identifies its values with the original integrand.

The only representation hypothesis here is smoothness of the test
representation, which is included in the full Whittaker-type hypothesis of the
convergence target. The block representations are arbitrary, and all supplied
functionals, including zero functionals, are retained. These are internal
topological consequences of the published constructions; no new assertion from
the original literature is needed.
