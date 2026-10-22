# Spectral bounds on the actual minimal polynomial: domain case

Author: Worker 56.

The theorem concerns a complete normed K-algebra B which is a domain
and finite and torsion free over an actual Tate algebra T. The scalar
tower is compatible and T to B is continuous. K is complete,
nontrivially normed and ultrametric. For an element whose values at
every point of the actual bounded multiplicative spectrum of B are at
most one, the theorem proves that every coefficient of its constructed
minimal polynomial over T has Gauss norm at most one.

The preceding factoriality and integral-closure constructions ensure
that this monic polynomial over T becomes the minimal polynomial over
the fraction field of T. The earlier Gauss-algebraic-closure construction
supplies an actual algebraically closed ultrametric field C into which
T maps isometrically. Every root in C of the mapped polynomial extends
to a homomorphism from the fraction field of B by Mathlib's algebraic
embedding-extension theorem. Restricting it to B gives a T-algebra map.

The finite Banach-algebra continuity theorem proves this map bounded;
pulling back the norm of C therefore gives an actual point of the
bounded multiplicative spectrum of B. The spectral hypothesis bounds
the chosen root by one. All roots, with their original multiplicities,
are treated this way. The split monic polynomial then belongs to the
polynomial ring over the actual norm unit-ball subring of C. Its
coefficients have norm at most one, and the isometry on T transfers
the bound to the original coefficients.

This follows the domain-case algebraic strategy of Proposition 2.6.1,
page 11, and Proposition 2.6.4, pages 11-12, of the retained
Berkovich-course notes. It supplies the norm-controlled relation rather
than assuming such a relation. The implementation uses the full
multiset of roots and needs no separability assumption. Continuity uses
the separately proved finite Banach presentation and the Banach open
mapping theorem.

`PrimeQuotientSpectralRelation` applies this result to prime quotients.
`SpectralPowerBoundProof` then combines their relations to treat arbitrary
presented affinoids, including nonreduced quotients.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
