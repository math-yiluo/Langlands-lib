# Normal localizations of a reduced Noetherian ring's normalization

Worker 594.

The proof shows that the total fraction ring of a reduced Noetherian
ring is Artinian. The inverse image of a prime of the total fraction
ring is disjoint from the non-zero-divisors. An element outside all
minimal primes is a non-zero-divisor, since a multiple that is zero
would force the other factor into every minimal prime. Prime avoidance
therefore puts the inverse image inside a minimal prime, so it is
minimal itself. Primes of the total fraction ring are then maximal,
which gives the Artinian property.

The reduced Artinian algebra splits as the product of its field
quotients. The definition `integralClosureEquivArtinianComponents`
restricts that isomorphism to integral closures. Integrality in the
product follows from integrality in each component by multiplying
the finitely many monic equations. The integral closure in each
field is an integrally closed domain, and localizing at a prime of
the product localizes the corresponding component.

For a flat finite-type algebra over a Noetherian domain with smooth
generic fibre, the map into the generic fibre is injective and the
generic fibre is reduced. The proof transports the normalization in
total fractions to the normalization in the generic fibre and
transports each local ring through this equivalence.

This is a derived normality result for the affine normalization
appearing in Conrad's appendix to Prasad–Yu, *On quasi-reductive
group schemes*, author preprint, Remark A.7 (p. 30). The registered
source is `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
