# Local multipliers and derivatives along smooth vector fields

`localScalarMultiplierCLM` multiplies a compactly supported test by a scalar function that is smooth on the open test domain. On each fixed compact support the multiplier agrees with a globally smooth extension obtained using a cutoff. The fixed-support maps therefore give a continuous linear map on the test space.

`smoothVectorFieldDerivativeTest` evaluates the Fréchet derivative of a test on a vector field smooth on the test domain. Its support lies in the support of the input test. For a finite variable-coefficient linear combination of fields whose derivatives a distribution annihilates, the Leibniz rule gives the identity for the combined field with a correction from the derivatives of the coefficient functions.

These are auxiliary test-function constructions for local conjugation descent in Aizenbud and Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, §§3.1 and 7.6. The local multiplier and derivative identity follow directly from the test topology and the differential product rule.
