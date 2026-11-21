# Normal stalks over an integrally closed domain

`SmoothNormalDomainStalksStatement` says that for an integrally closed
domain `R` and a smooth morphism `p : X ⟶ Spec R`, each actual stalk of
`X` is an integrally closed domain. The ring and scheme lie in the same
arbitrary universe.

The proof selects a chart in the affine cover containing the chosen
point. Its coordinate algebra is smooth over `R`, by the global
sections isomorphism of `Spec R` and the affine characterization of
smoothness. Its stalk is the prime localization of the coordinate
algebra. The published FLT port for prime localizations of smooth
algebras over integrally closed domains makes the chart stalk an
integrally closed domain. The chart map is an open immersion, so the
stalk isomorphism transports both properties to the required stalk.

The companion `isIntegral_of_smooth_geometricallyConnected` uses the
published geometric integrality of smooth geometrically connected
fibres. A smooth morphism is open, so geometrically irreducible fibres
over an irreducible base imply irreducibility of the source. The
published reducedness result for a smooth morphism over a reduced base
then gives integrality when the base is integral.

Both results are internal scheme-level consequences of the imported
algebraic and geometric results. In the relative torus application
the base ring is a valuation domain, which is integrally closed.
