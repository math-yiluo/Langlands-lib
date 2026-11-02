# Rational charts as a dense subsite of full represented domains

Author: Worker 36.

This construction uses the finite full-domain topology and the
existing finite rational topology over one actual positive-polyradius
presented affinoid algebra `A` over a complete ultrametric normed field `K`.
The existing `toDomainFunctor K A` retains every rational quotient algebra,
its bounded structural map and every actual bounded restriction. It is
already fully faithful.

`isFiniteCovering_functorPushforward_iff` proves that a rational sieve covers
precisely when its generated image sieve covers in the full-domain site.
Forwards from the full-domain site, apply unconditional rational refinement
to a finite covering witness. Lift each resulting arrow through the fully
faithful functor. Its membership follows from the equality between a sieve
and the pullback of its image under a fully faithful functor. In the other
direction the same finite family of rational charts, retaining its arrows
and loci, witnesses coverage of the image sieve.

The functor is cover dense: the published finite rational-cover theorem
supplies actual rational arrows covering every full-domain locus, and
each of these arrows factors through a rational image object by its identity.
These two results, with the existing full faithfulness, construct Mathlib's
`IsDenseSubsite` instance for the independently defined topologies.

`functorPullback_mem_finiteRationalTopology_iff` identifies covering sieves
exactly on restriction. One direction pushes the rational covering back
into the given full-domain sieve. The other uses cover lifting.
`toDomainFunctor_inducedTopology` identifies the topology induced on
rational charts with the original finite rational topology.

For any value category `B`, `domainSheafRestriction K A B` is the continuous
direct image along the rational inclusion: it evaluates a sheaf at the
actual rational quotient objects and precomposes its restriction maps.
The functor is full and faithful without a limit hypothesis on `B`.
The object formula states this evaluation literally.

`finiteDomainHypercoverData U` supplies explicit small 1-hypercover data.
The degree-zero family is a chosen finite ambient rational cover of `U`.
For each pair of members the degree-one family has one object, their actual
product-radius rational intersection, and the two constructed bounded
projections. Uniqueness of full-domain arrows proves the triangle over `U`.
For two rational arrows into those members, locus containment constructs
their lift into the intersection. Uniqueness of rational arrows proves its
two projection equations. Thus the degree-one comparison sieve contains the
identity and covers. Both index types lie in `Type 0`, even when `K` lies
in an independent larger universe. Empty degree-zero covers are allowed.

This data proves `IsOneHypercoverDense.{0}`. If `B` has limits of size
`(0, 0)`, `domainSheafEquivalence K A B` applies Mathlib's 1-hypercover
comparison theorem. Its inverse is exactly `domainSheafRestriction K A B`.
No limits indexed by the large full-domain category or its structured-arrow
categories are assumed. The module does not yet identify the comparison
extension with the original stored full-domain quotient-algebra presheaf.

This is internal categorical packaging of the full-domain finite topology,
the proved ambient rational refinement and the published fully faithful
rational-domain inclusion, using Mathlib's dense-subsite comparison.
No private peer draft or additional original-literature assertion is used.
The sites remain over one fixed affinoid; this does not construct analytic
atlases, etale sites, equivariant sites or their cohomology.
