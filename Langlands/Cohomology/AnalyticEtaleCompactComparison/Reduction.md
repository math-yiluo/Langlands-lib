# Exact remaining inputs to the compact analytic étale comparison

This is an internal composition of the existing support, local
action and derived comparison constructions. It asserts no new theorem from
external literature. The underlying source proposition remains Berkovich's
Corollary 1.5.2(i), as documented in the unchanged statement module.

Fix a complete ultrametric normed field `K`, a normed extension field `L`, an
analytic space `X`, point axioms `h` at every `L`-valued point of `X`, a
topological group `G` with the prescribed smallness, an action `ρ` with
admissible refinements, and a commutative coefficient ring in universe
`max u (v + 1) uL`. The field, space, extension and group universes are
independent and match the statement modules.

`globalAcyclic_of_compactAcyclic` takes the compact-support acyclicity
statement as a premise and proves its compact-space ordinary counterpart.
For each compact Hausdorff space in that counterpart, it applies the compact
premise to the same injective equivariant sheaf and positive degree. The
vanishing equivalence obtained from
`etaleCompactCohomologyIsoOfCompactSpace` transfers this vanishing to actual
ordinary étale cohomology of the restricted sheaf. It uses the supplied `h`
and surjectivity of `pointProjection`. Consequently this theorem retains `h`
as a proof input even though its resulting standalone global proposition
does not bind `h`. No existence of a point field or of its point axioms is
proved. `acyclic_iff_compactAcyclic` packages this transfer with projection
from the conjunction, showing that the combined acyclicity statement reduces to
its compact-support component when `h` is given.

`compactComparison_of_openDomains_of_openMap_of_compactAcyclic` concludes the
exact `AnalyticEtaleCompactComparisonStatement` from three explicit
premises:

- `EtaleOpenDomainStatement X`, étaleness of the canonical inclusions of open
  analytic domains for the existing all-affinoid-pieces definition;
- `EtaleOpenMapStatement K`, openness of the actual underlying maps of all
  étale morphisms, in the original independent field and space universes;
- `AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R`,
  actual compact-support acyclicity after restriction of injective étale
  equivariant sheaves.

For the Hausdorff and surjectivity assumptions of the target, the first
premise and `h` give `EtalePointLifting` by
`etalePointLifting_of_openDomains`. The second premise gives openness of the
structural map of every étale site object.
`isIso_etaleCompactInclusion` (in
`Langlands.Sheaf.Equivariant.AnalyticEtaleCompactLocal`) therefore supplies the canonical degree-zero
isomorphism: local discreteness fixes compactly supported sections under an
open subgroup. The third premise supplies compact acyclicity of the same
restricted injectives. The Library's
`isIso_etaleCompactComparison_of_injective_acyclic` then gives invertibility
of the canonical comparison in every degree. Continuity of the action and
Hausdorffness enter precisely through these stated inputs; no extra
hypothesis is added to the final proposition.

`compactComparisonIsoOfOpenDomainsOfOpenMapOfCompactAcyclic` packages this
invertibility as an actual natural isomorphism. Besides the three remaining
inputs, it takes Hausdorffness, surjectivity of `pointProjection`, continuity
of the action and a degree `q`. Its functor endpoints are

```text
etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G
  ≅ etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q.
```

The construction uses `asIso` on the canonical comparison after supplying
the preceding theorem's `IsIso` result. The theorem with suffix `_hom`
identifies its forward transformation with
`etaleCompactComparison L ρ h R q` by definitional equality.

All three premises remain unproved in this module. This conditional
reduction is not a proof of Berkovich's comparison without those inputs.
It assumes neither comparison theorem and does not assert that restriction
preserves injectives. The compact/global transfer concerns actual right
derived functors, rather than an auxiliary cohomology theory.
