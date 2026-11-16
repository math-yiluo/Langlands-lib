# Godement inputs and reduction for restricted-injective acyclicity

This internal statement and reduction unit isolates two analytic obligations
for `AnalyticEtaleRestrictedInjectiveAcyclicStatement`. It proves the reduction,
not the two obligations or the unconditional target.

The parameters are exactly those of the target: a complete ultrametric normed
field `K`, a normed extension field `L`, an analytic space `X`, point axioms `h`
for all its `L`-valued points, a topological group `G` acting through `ρ`, and
a commutative coefficient ring in universe `max u (v + 1) uL`. The Godement
statement and the reduction theorems explicitly retain `IsTopologicalGroup G`,
smallness in that universe, and admissible refinements of the distinguished
lift system. No equality of universe levels is imposed.

`AnalyticEtalePointFibersJointlyFaithfulStatement` asserts that, when `|X|`
is Hausdorff and `pointProjection L X` is surjective, the actual functors
`(etalePoints L h x).sheafFiber` jointly detect equality of morphisms between
all étale module sheaves. This concerns every object of the site; the published
detection theorem for sections over `etaleSelf X` does not establish it.
No equivariant category or action occurs in this obligation.

`AnalyticEtaleGodementCompactAcyclicStatement` asserts that, under Hausdorffness,
surjectivity of the point projection and continuity of the action, every
degree-zero term of the actual equivariant functor
`etaleGodementZeroFunctor L ρ h R`, after `etaleGSheafRestriction ρ R`, has zero
`etaleCompactCohomology L h R (q + 1)` for every natural number `q`.
The input sheaf is arbitrary; its injectivity is not assumed. The Godement
functor uses the lifted actual point family, the twisted-site Godement
construction and the locally discrete coreflector described in
`AnalyticEtaleGodement`. This statement asserts actual right-derived
compact-support vanishing and does not define acyclicity to mean softness.

The provenance of both statements is internal: they isolate the remaining
premises in the published Godement-retraction proof route for the parent
target. They are not attributed as verbatim theorems of the literature, and
neither is proved here. An analytic softness interface, its Godement theorem
and a comparison of supported derived functors would be possible further
prerequisites for the second statement.

`analyticEtaleRestrictedInjectiveAcyclic_of_compact` proves that the compact
acyclicity assertion supplies the entire target conjunction.
On a compact underlying space, surjectivity of `pointProjection` identifies
compact-support bounds in the induced point topology with bounds by compact
subsets of `|X|`. In particular, the whole space bounds every section.
The published `etaleCompactSectionsIsoOfCompactSpace` is the inclusion of
compactly supported sections in all sections, and
`etaleCompactCohomologyIsoOfCompactSpace` derives this natural isomorphism.
The implemented proof applies its vanishing equivalence
`isZero_etaleCompactCohomology_iff_of_compactSpace` in degree `q + 1` to
the restriction of the given injective sheaf.
The theorem retains `h` as an input even though the global component of its
conclusion does not bind `h`. The reverse implication is the first projection
of the conjunction; `analyticEtaleRestrictedInjectiveAcyclic_iff_compact`
records the equivalence.

Finally, `analyticEtaleRestrictedInjectiveAcyclic_of_godement` assumes the two
explicit analytic statements. Joint faithfulness invokes the published
`mono_etaleGodementCoaugmentation_of_jointlyFaithful`. An equivariantly
injective sheaf retracts from its Godement term along this monomorphism.
The published
`isZero_etaleCompactCohomology_restriction_of_godementZero` maps that retraction
through restriction followed by the actual compact-support cohomology functor,
so vanishing passes to the retract. Applying the first reduction supplies the
ordinary component on compact spaces as well.

All these reductions are independent of
`AnalyticEtaleCompactComparisonStatement` and
`AnalyticEtaleGlobalComparisonStatement`. They neither assert that restriction
preserves injectives nor assume either comparison. The unresolved point-family
and Godement-term vanishing premises remain explicit.
