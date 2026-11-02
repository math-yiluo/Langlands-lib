# Local surjectivity for actual etale scheme presentations

These internal derived helpers use the actual big etale topology on
`Over S` and the published algebraic-space predicates for representable
etaleness and geometric surjectivity. They adapt the covering-sieve
arguments in `AlgebraicSpace.FppfQuotientRepresentability` to the etale
topology. The base and every test object are arbitrary schemes.

`generate_singleton_mem_etaleTopology` proves that a single actual
surjective etale scheme morphism over `S` generates a covering sieve.
The slice sieve equivalence reduces this to the underlying scheme.
Mathlib's singleton precoverage criterion applies because the underlying
morphism is etale and surjective.

`isLocallySurjective_etale_schemeYoneda_map` shows that the transformation
of lifted represented presheaves induced by such a morphism is locally
surjective. For each test scheme and each represented section, the
pullback of the covering sieve consists of morphisms along which that
section lifts.

`isLocallySurjective_etale_of_isEtale_isSurjective` treats any transformation
of actual presheaves satisfying the published geometric etaleness and
surjectivity predicates. For any section of its target, lifted Yoneda
supplies a transformation from the test scheme's represented presheaf.
The chosen scheme representing its pullback projects etale and
surjectively to the test scheme. Evaluating the pullback square at the
identity gives a lift along that covering projection. No sheaf condition
on either presheaf is used.

`exists_iso_of_common_etale_presentation` applies the imported
`CategoryTheory.Sites.CommonKernelComparison` to two etale sheaves presented
by the same scheme over `S`. It assumes both presentation maps are locally
surjective for the etale topology and have precisely the same kernel on
morphisms from every actual test scheme. The scheme's fppf represented
sheaf restricts to an etale sheaf; its underlying presheaf is the published
lifted scheme Yoneda presheaf. The general comparison lemma therefore
produces an isomorphism of the two presheaves compatible with both
presentations.

`commonEtalePresentationIso` names an actual such isomorphism, using
classical choice from the existence theorem. The theorem
`commonEtalePresentationIso_hom_fac` proves that composing its forward
map with the first presentation gives the second presentation. Thus the
definition supplies data in the presheaf category, including its inverse
and both inverse laws.

`isSheaf_fppf_of_common_etale_presentation` specializes the second sheaf to
an actual fppf sheaf. It is also an etale sheaf by the inclusion of
topologies. The comparison isomorphism transports the fppf sheaf condition
to the first presheaf.

These helpers construct no etale equivalence relation quotient. In the
last result, the fppf sheaf and its etale-local presentation with the
specified kernel are assumptions that must be supplied separately.
The lemmas do not establish the fppf sheaf condition for an arbitrary
etale sheaf. Their provenance is the published actual presheaf interfaces,
the earlier fppf covering-sieve and common-kernel helpers, and Mathlib's
definition of the big etale topology and sheaf theory.
