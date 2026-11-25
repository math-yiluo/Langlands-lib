# Weak standard integrals under literal subgroup comparison

This internal adapter extends the published
`DynamicCommonLeviStructuralComparison` maps. It is a derived formal transport
module for the actual common-Levi presentation reduction from Waldspurger IV.1.1,
rather than an additional source theorem. The source context
is Waldspurger (2003), IV.1, printed pp.276–278, registered as
`waldspurger-2003-plancherel`. It proves no analytic convergence theorem.

`representationOfEq_isAdmissible` and `representationOfEq_hasFiniteLength`
transport the two finiteness properties through the constructed identity on
ambient Levi elements, preserving the inducing carrier. After eliminating the
subgroup equality, both properties are the original properties.

`integrandComparisonOfEq` compares the actual quotient integrands for every
ambient argument through `leviInductionComparisonOfEq` and
`quotientComparisonOfEq`. In particular, applying any linear scalar functional
gives the same scalar integrand. `hasIntegralComparisonOfEq` identifies scalar
absolute integrability and represented weak integrals with the original
carrier, using the exact measure `quotientMeasureOfEq`. Eliminating the literal
subgroup equalities turns the quotient map into the identity and the measure
into its pushforward by the identity; `Measure.map_id` proves the measure
comparison without a normalization factor.

`memDomainComparisonOfEq` uses `StandardIntertwining.mem_domain` and the
weak-integral equivalence to compare the whole domains. The construction
`domainComparisonOfEq` restricts the constructed induction linear equivalence
to these domains using `LinearEquiv.ofSubmodules`. Its coefficient formula
`domainComparisonOfEq_coe` is definitionally the original induction map.
The full-domain
equivalence also follows by equality elimination and the same exact measure
identity. `operatorComparisonOfEq` transports `operator_spec` and uses
`operator_eq`, so the selected represented integral agrees at every ambient
argument. No representation equivalence or family equality is a premise.

`squaredModulusComparisonOfEq` transports the entire squared-modulus
compatibility proposition through the literal subgroup equalities. Its proof
eliminates those equalities; proof irrelevance identifies the displayed
semidirect decompositions and closedness witnesses.

The direct mathematical dependencies are the published
`representationOfEq`, `leviInductionComparisonOfEq`,
`quotientComparisonOfEq`, `quotientMeasureOfEq`,
`StandardIntertwining.integrand`, `HasIntegral`, `domain`, `mem_domain`,
`operator_spec`, `operator_eq`, and `SquaredModulusCompatibility`, together
with Mathlib's identity measure pushforward. The group universe and inducing
carrier universe are independent.
