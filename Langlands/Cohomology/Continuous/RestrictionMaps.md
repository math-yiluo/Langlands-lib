# Restriction on finite quotient cohomology

Author: Worker 22. The imported comparison definition is published at
`1058c134c0d2fb45ec96d08ea2956983aaac1d80`; the subgroup finite-stage
infrastructure is published at `68e8013fc4fed0de284fd849695676aca2e0c32d`.

`finiteQuotientRestriction A H q` is the colimit map constructed from
ordinary restriction at finite quotient stages. Here `G : Type u` is a
topological group, `k : Type u` is a commutative ring with a topology,
`A : DiscreteModule k G` has the specified jointly continuous discrete
action, and `H : OpenSubgroup G` has the inherited topology.

For an open normal subgroup `N`, the actual quotient homomorphism
`H / (H ∩ N) → G / N` is `quotientSubgroupMap`. The coefficient morphism
`fixedSubgroupRestriction` sends an `N`-fixed vector to the same vector
fixed by `N.comap H.subtype`. Quotient induction verifies equivariance.
It does not require `N ≤ H`; hence this is a coefficient morphism, and
no inverse is asserted.

`finiteRestrictionCochains` applies Mathlib's ordinary `cochainsMap` to
that pair. `finiteRestriction` is its homology map. The refinement
certificate is proved first on cochains, using composition of the actual
group and coefficient maps, and then on homology. Together with
`finiteStageToColimit_refinement`, this supplies the naturality certificate
of `finiteRestrictionCocone`. The universal colimit map of this cocone
is the selected `finiteQuotientRestriction`.

`continuousRestrictionCochains` is Mathlib's continuous cochain map for
the subgroup inclusion and identity coefficient morphism, with topology
forgotten. The continuous cohomology restriction remains the already
published `continuousRestriction`, which is defined by the actual
`ContinuousCohomology.map`. The compatibility of these named maps is the
separate proposition `RestrictionComparisonLaws`.

Compactness is not required to define these diagrams and maps. Under
compactness their quotient stages are finite. All degrees are natural
numbers, and all carriers retain the arbitrary common universe `u`.

This infrastructure is derived from Serre, *Local Fields* (1979), VII §5,
printed pp.115–117 / PDF pp.121–123 (restriction and inflation), and
X §3, printed p.154 / PDF p.160 (the inflation-indexed limit).
The naturality and cocone calculations described above are implementation
certificates for this exact Mathlib model.

Literature ID `serre-1979-local-fields`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
