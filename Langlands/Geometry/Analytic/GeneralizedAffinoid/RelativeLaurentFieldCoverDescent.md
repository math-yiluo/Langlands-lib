# Rational-cover descent from the independent Laurent coefficient field

This internal construction transports rational charts from the actual
coefficient-field presentation to the actual relative Laurent annulus, then
applies the existing Gauss-section descent. It assumes a complete ultrametric
normed field, a positive Laurent radius, and the same integer-power independence
condition as `RelativeLaurentFieldDomain`. All Laurent constructions retain
universe `u`.

`RationalChart.ringPullback` allows the two displayed coefficient fields to
differ, even in universe. It maps the actual denominator and numerator classes
through a bounded unital ring homomorphism and chooses representatives in the
target presentation. Unit generation follows by pulling back the target
generated ideal: it contains every original generator, hence contains one.
`ringPullback_locus` identifies the resulting inequalities exactly with the
inverse image under the bounded spectrum map. This construction concerns the
displayed rational data and its actual rational quotient; it asserts no quotient
comparison across fields.

`annulusChart` applies that construction to the actual bounded inverse map
`fromPresentation`. Its locus is exactly the inverse image under the inverse
ambient spectrum homeomorphism. `annulusToFieldLocus` restricts this continuous
map to the actual domain loci; its well-definedness uses the inverse identity
and the definition of `fieldLocus`.

If a coefficient-field chart is contained in the full coefficient-field domain,
its annulus chart is contained in the full lifted domain by the exact locus
identity. `annulusChartMap` uses full domain representation to construct an
actual bounded restriction with its equation over the ambient annulus algebra.
`annulusFiniteRationalCover` transports a finite chart family, its restrictions,
and its covering property. `fieldFiniteRationalCoverDescent` then applies the
previously proved finite Gauss rational-pullback construction to obtain an
actual finite ambient rational cover of the original domain.

`fieldDomainGaussSection` composes the continuous domain Gauss section with the
inverse ambient spectrum homeomorphism. For a finite-union rational neighborhood
in the coefficient-field domain, `annulusFiniteRationalNeighborhood` pulls the
neighborhood back continuously. Its exact preimage is the finite union of the
transported annulus chart loci, with the restrictions just constructed.
`fieldFiniteRationalNeighborhoodDescent` applies the previous annulus descent.
`fieldRationalNeighborhoodDescent` first treats a single chart as a one-member
family. The conclusion is a finite-union neighborhood over the original field.

The provenance is internal: only actual coefficient representatives, the
unit-ideal argument, the established bounded scalar-extension equivalence, full
domain representation and the previous rational Gauss descent are used.
Arbitrary positive original and rational radii, arbitrary closed ideals, trivial
original valuations and zero or nonreduced quotients remain allowed. These are
descent constructions; they do not establish the existence of covers upstairs,
strictification, or the host finite rational-cover proposition.
