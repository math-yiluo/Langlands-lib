# The density at the actual lower compact

For a Weyl representative in the weak expansion, the conjugated inducing
Levi lies in the prescribed lower ambient Levi. The isomorphism
`lowerParameterIso` identifies the lower dynamic parameter scheme with
the original inducing Levi scheme. Transporting the original split
component along the inverse isomorphism gives a split component of that
parameter scheme.

On points its image is exactly the conjugate central subgroup used by
`lowerCentral`. The proof uses the actual parameter isomorphism on points,
the conjugation homeomorphism and the equality between the point map of a
composition and the composition of the two point maps.

`lowerDensityFromOppositeContinuations` uses the compact intersection in
the lower Levi and the Iwasawa products there for both opposite
parabolics. It applies the density constructor to the conjugated
representation, the just-identified split component and the original
transported quotient Haar measure. The existing square-integrability
transport supplies the analytic input to that constructor. The two
full-domain continuations and their nonempty open convergence subsets at
this compact remain explicit.

This derived construction supplies the lower density package in the
Waldspurger VI.3.1 weak expansion. The output uses the literal lower
group, original conjugated inducing data and the compact intersection
specified by common source normalization.
