# Rational representation with presented strict affinoid tests

Author: Worker 36.

`Langlands.Analytic.StrictTestDomain.RationalRepresentationStatement`
is a proposition quantified over a complete ultrametric normed field `K`,
a presented strict affinoid algebra `P`, and `d : RationalData K P`.
The data consist of a finite numerator tuple and a common denominator in
the actual algebra `P`, together with their absence of common zeros on
its bounded multiplicative seminorm spectrum.

The assertion is `Represents K d.baseMap d.locus`. It has three clauses:

- The rational locus defined by `x(d.numerator j) ≤ x(d.denominator)`
  for every numerator index is closed in the spectrum of `P`.
- Pullback of seminorms along the constructed bounded map `d.baseMap`
  has image exactly that locus.
- For every presented strict affinoid algebra `R` and bounded algebra map
  `φ : P → R` whose spectrum image lies in that locus, there is exactly
  one bounded algebra map `ψ : d.algebra → R` with
  `ψ.comp d.baseMap = φ`.

The representing algebra and structural map are the existing constructed
closed-ideal quotient of an enlarged finite Tate algebra and its bounded
map. They are not existential input objects. No separate unit-ideal
certificate, inverse denominator, solution tuple, power bound or
factorization is assumed. Uniqueness is equality of bounded algebra maps.
The base, representing and test algebras have carriers in the coefficient
universe; their finite presentation data are independent. Zero quotients,
nilpotents, empty numerator tuples and trivial scalar valuations are allowed.

This is a derived specialization of Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), Definition 2.2.1 and Exercise 2.2.2(ii),
printed/PDF page 9. Definition 2.1.11 on page 8 gives the opposite
bounded-algebra-map interpretation of morphisms. The exercise supplies
the no-common-zero premise and rational inequalities; the definition
supplies the closedness, image and unique-factorization requirements.
The intended derivation combines the spectrum criterion for unit-ideal
generation, rational spectrum identification, closedness of the rational
inequalities and bounded factorization for presented strict affinoid tests.
This file defines the target proposition and supplies no proof.

The test objects here are only presented strict affinoids, and all rational
radii are one. Even the source's strictly affinoid domains must satisfy
the universal property for all affinoids. That stronger claim is not made.
Comparison of the enlarged Tate quotient with the source's relative
power-series presentation, arbitrary positive radii, general affinoid
tests, structure sheaves, analytic atlases and sites remain separate work.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
