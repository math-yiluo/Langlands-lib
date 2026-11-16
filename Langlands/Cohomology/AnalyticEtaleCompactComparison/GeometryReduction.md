# Compact analytic étale comparison from restricted-injective acyclicity

Worker 515. This internal construction applies the published geometric proofs
to the existing [comparison reduction](Reduction.md). It introduces no
external-source assertion.

The parameters are those of `AnalyticEtaleCompactComparisonStatement`: a
complete ultrametric normed field `K`, a normed extension `L`, an analytic
space `X`, the supplied point axioms `h`, a topological group `G` with the
specified smallness, an action `ρ` with admissible refinements, and a
commutative coefficient ring `R`. The independent universes `u`, `v`, `uL`
and `z` and the coefficient universe `max u (v + 1) uL` are retained.

`compactComparison_of_compactAcyclic` proves the exact comparison proposition
from the explicit premise
`AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R`.
That premise says that, under the target's Hausdorffness, point-projection
surjectivity and continuous-action hypotheses, positive-degree actual plain
compactly supported cohomology vanishes on the restrictions of injective
étale equivariant sheaves. Injectivity is in the equivariant category.

The implemented proof supplies `etaleOpenDomainStatement X` from
`Langlands.Geometry.Analytic.EtaleOpenDomains.Proof` and `etaleOpenMap K`
from `Langlands.Geometry.Analytic.EtaleOpenMap.Proof` to
`compactComparison_of_openDomains_of_openMap_of_compactAcyclic`.
Thus open-domain étaleness and openness of étale maps are proved inputs,
with no remaining geometric premise. The reused reduction obtains the
degree-zero canonical inclusion isomorphism from these geometric facts,
`h` and point-projection surjectivity, and applies the derived comparison
criterion with the supplied restricted-injective compact acyclicity.

`compactComparisonIsoOfCompactAcyclic` packages this result as a natural
isomorphism in each degree `q`, with the original Hausdorffness,
surjectivity and continuity hypotheses supplied:

```text
etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G
  ≅ etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q.
```

It specializes the existing natural isomorphism to the same two published
geometry proofs. The theorem `compactComparisonIsoOfCompactAcyclic_hom`
identifies its forward transformation with
`etaleCompactComparison L ρ h R q` by definitional equality.

Restricted-injective compact acyclicity remains an explicit unproved input
to this module. This conditional construction does not prove the
unconditional comparison statement or assert that restriction preserves
injectives. The target statement and all its imports are unchanged.
