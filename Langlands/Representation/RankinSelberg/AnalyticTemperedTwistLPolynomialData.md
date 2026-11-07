# Real-twisted analytic tempered polynomial data

Author: Worker 111.

This internal construction applies the published unramified-twist transport
twice to the original-action analytic tempered L-polynomial. For irreducible
analytically tempered actions `π` and `σ`, and real exponents `s` and `z`,
it constructs a polynomial with the full existing symmetric L-polynomial
certificate for their actual determinant twists. It has no zeros in the
open disk of radius `q^(s+z)`, where `q` is the canonical residue cardinality.
Independent field and carrier universes, both rank orders, the supplied
additive character and the supplied self-dual Haar measure are retained.

`realPowerTwistLPolynomial` identifies the real-power character with the
complex unramified character using `Complex.ofReal_cpow`. The two published
twist operations substitute `q^(-s) X` and then `q^(-z) X` into the same
polynomial. The constructor uses this actual nested substitution and
retains its full certificate. At a point `w` in the stated disk, the
substitution point has norm `q^(-(s+z)) * ‖w‖ < 1`. The original analytic
tempered polynomial does not vanish there. Positivity of `q`, real-power
addition and inversion justify the norm calculation.

`analyticTemperedTwistLPolynomial_poleFree` transfers this disk bound to
every certificate of the same twisted pair by polynomial uniqueness.
No polynomial, Whittaker type, pole bound or classification hypothesis is
added to the constructor's irreducibility and analytic temperedness inputs.
This unit supplies block root bounds for the standard-module product proof;
it makes no assertion about that product.

The provenance is internal composition of
[the original-action analytic adapter](AnalyticTemperedLFactor.md) and
[the proved unramified-twist transport](UnramifiedTwistLFactorProof.md),
using [the actual real-power twists](../Twist/RealPower.md) and elementary
Mathlib norm and real-power identities. It introduces no external assertion.
