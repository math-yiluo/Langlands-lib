# Lower packet densities at the literal inherited compact

`LowerPacketDensityAtCompactStatement` asserts that square integrability
modulo the actual inducing split component and the standard Levi Iwasawa
products give an actual density package at the lower compact. Its inducing
representation is the conjugated representation on the dynamic Levi.
The compact of the package is the literal preimage of the given compact
under the standard Levi inclusion. The package includes the two continuation
data on the full domains of the actual integrals, together with the density's
openness, irreducibility and unitary-regularity fields.

`lowerPacketFullDomains_nonemptyInterior` constructs a positive invariant
form for the conjugated square-integrable representation by
`squareIntegrableCentralSubgroupForm`. It uses the transported quotient Haar,
irreducibility and the modular character of the lower dynamic Levi. The
`commonLeviContinuationExists_of_unitarizable` theorem in the two orders of
the opposite parabolics gives nonempty open subsets of the respective domains
on that same compact. `interior_maximal` puts these subsets inside the interiors.

If both entire domains are open,
`lowerPacketDensityAtCompact_of_isOpen_fullDomains` combines these nonempty
interiors with `exists_lowerDensityPackage_at_compact_of_openFullDomains` to
construct the package. The domain-openness hypothesis concerns the entire
actual domain. The existence of open subsets is a separate property.

The existence target is an internal input to Waldspurger (2003), VI.3.1,
printed p. 304, where the weak constant term is expressed using lower-Levi
packets. Its proof route specializes the bounded-coefficient IV.1.1
construction (printed pp. 277–281). The exact continuation data of the
Library's density package specify agreement and nonvanishing of the chosen
denominator on the entire convergence domain.
