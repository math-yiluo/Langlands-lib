# Rational algebra actions around a pullback square

Given a rational algebra action over \(S\) and two factorizations
\(Z\to W\to S\) and \(Z\to W'\to S\) of the same map, `pullbackSquareIso`
compares the two iterated pullbacks. It reverses the direct-to-iterated
comparison for the first factorization, transports the direct pullback along
the equality of base maps, and applies the direct-to-iterated comparison for
the second factorization.

`hom0_pullbackSquareIso_hom` identifies the underlying rational
homomorphism with the rationalization of the corresponding abelian-scheme
isomorphism `baseChangeSquareIso`. It uses the underlying maps of the two
composition comparisons, and reduces the equality-transport comparison to
the identity by substitution. `square_compatible_of_iso_eq` applies `hom0` to
the commutativity equation and rewrites the maps of the comparisons and the
pulled-back isomorphisms.

`exists_iso_of_etale_rationalHomDescent` takes an étale cover by connected
locally noetherian schemes and equivariant rational isomorphisms between the
restrictions of two fixed rational actions. The isomorphisms must commute with
the comparisons on all connected locally noetherian common tests. The
theorem assumes `ConnectedEtaleRationalHomDescentStatement` and injectivity of
rational Hom pullback to one chosen member. It applies rational Hom descent
to the forward and inverse maps, using the inverse commutativity equation
for the latter. The inverse equations and equivariance of the descended maps
follow by injectivity on the chosen member. `isoMk` then gives an
equivariant rational isomorphism whose restrictions are the given ones.
