# Locally constant sheaves on finite weighted rational sites

Author: Worker 56. Internal derivation from the actual rational chart category,
the published finite-cover quotient criterion and the original-domain
locally constant sieve-gluing construction.

`locusLocallyConstantPresheaf` assigns the entire set
`LocallyConstant d.locus C` to each actual positive-radius rational chart.
`spectrumLocallyConstantPresheaf` assigns the entire set of locally constant
functions on its original quotient spectrum. The two presheaves pull back
along the original locus inclusions and bounded spectrum maps.
`locallyConstantPresheafIso` uses the original rational spectrum-locus
homeomorphism in both directions. The four evaluation lemmas retain these
original maps explicitly. These presheaves and their comparison do not
require completeness of the coefficient field.

`isLocallyConstant_iff_of_finite_cover` treats any finite type-indexed family
of actual rational restrictions whose loci cover the target points.
It uses `RationalChart.toDomainFunctor` and `Domain.FiniteCover.ofFintype`
to retain the original representing quotient algebras, bounded maps and
loci, with a finite-ordinal reindexing. The published
`Domain.FiniteCover.isOpen_iff_loci` detects openness on all component
loci from the finite disjoint-union spectrum quotient. Applying this to
the preimage of each coefficient subset detects local constancy on the
target from local constancy of every locus pullback. This proof permits
an index universe independent of the field and coefficient universes.

For an arbitrary sieve containing a finite covering family,
`IsFiniteCovering.exists_mem` gives an actual sieve member through any
target point. `locusLocallyConstantCompatible_apply` evaluates matching
on the actual rational intersection of two arbitrary sieve members.
Uniqueness of the original bounded restriction makes the required
triangle commute, and the intersection locus contains each common
ambient point. Thus the two local functions agree there.

`exists_locusLocallyConstantSieveValue` constructs the coefficient value
at each target point and proves its agreement with every sieve member
containing that point. `locusLocallyConstantSieveGlueFun` chooses those
values. `locusLocallyConstantSieveGlue` applies the finite-cover criterion
to prove local constancy in the original target subspace topology.
Its restriction recovers every member of the entire sieve.
`locusLocallyConstantSieveGlue_unique` uses point coverage to prove that
any amalgamation has exactly these values.

`locusLocallyConstantPresheaf_isSheaf` proves Mathlib's sheaf condition
on the existing `finiteRationalTopology` by this existence and uniqueness
argument. `spectrumLocallyConstantPresheaf_isSheaf` transports the property
through the original natural comparison. `locusLocallyConstantSheaf` and
`spectrumLocallyConstantSheaf` package the resulting Type-valued sheaves,
and `locallyConstantSheafIso` lifts that same presheaf isomorphism to
an isomorphism of sheaves.

The sheaf and finite-cover proofs require a complete ultrametric
coefficient field. No coefficient element, topology, action, or
nonemptiness assumption is used. Empty coefficient sets, loci, and finite
covers of empty targets remain allowed. The site's finite witnesses use
its existing field-universe convention; the finite-family local-constancy
criterion itself allows an independent index universe.

Geometric conventions come from Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
printed/PDF p.4 Example 1.2.2(v), Definitions 1.2.3/1.2.5; pp.7-8
Definitions 2.1.2/2.1.11; pp.9-10 Definition 2.2.1,
Exercise 2.2.2(ii), Fact 2.2.3(i), Definition 2.2.7. These specify
positive-real-radius affinoid presentations, bounded spectra and maps,
and represented rational domains. The categorical sheaf and sieve
gluing constructions here are internal, not claims attributed to these
passages.

Rational charts retain their explicit unit-generation data, arbitrary
positive real radii, actual closed quotient by the equations
`g * Y_j - f_j`, bounded restrictions and original quotient topologies.
The stored unit-generation condition implies the source's absence of
common zeros; this construction claims no converse. Trivial valuations,
nilpotents and zero quotient algebras remain included. This unit constructs
locally constant function sheaves on the restricted finite rational site;
general analytic algebra sheafness, analytic atlases, full analytic sites,
group-action topology, etale and quasi-etale sites and the Harris tower
remain separate.
