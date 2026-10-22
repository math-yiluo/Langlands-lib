# The source comparison for continuous corestriction

Author: Worker 22. This is derived infrastructure for the continuous
corestriction construction. It uses the published finite-quotient comparison
and the proved finality of the ambient indexing functor. It does not define
corestriction or assert its refinement or transfer laws.

For a compact topological group `G`, an open subgroup `H`, a representation
`A : Rep k G`, and a natural degree `q`, `transferSourceDiagram A H q`
is the composite of `transferIndexFunctor H` with the actual subgroup
finite-quotient cohomology diagram. If `C` is the ambient normal core of
`H`, its stage at an ambient open normal subgroup `N` is

```
H^q(H / (H ∩ (C ∩ N)), (Res_H A)^(H ∩ (C ∩ N))).
```

Its arrows are the actual inflation transitions of the subgroup diagram,
with their fixed-coefficient inclusions. The normal core forces `C ∩ N`
to lie in `H`. Finality of this particular functor is already proved
in `SubgroupFiniteStages`; no cofinality hypothesis is added here.

For `G` compact and `A : DiscreteModule k G`,
`transferSourceComparisonIso A H q` identifies the colimit of this
diagram with Mathlib's actual `continuousCohomology` of the restricted
module, after forgetting from `TopModuleCat k` to `ModuleCat k`.
The isomorphism first uses `Functor.Final.colimitIso`, then the published
`finiteQuotientComparisonIso`. The open subgroup is closed, hence compact;
compactness supplies the local compactness needed for the latter comparison.
No Hausdorff hypothesis is needed. Both scalar and group types and the
coefficient carrier have the arbitrary common universe `u`. Every
natural degree, including zero, is supported.

`transferSourceComparisonIso_ι` proves that the forward isomorphism
composed with a colimit injection is exactly `finiteStageToContinuous`
for the restricted normal subgroup `H ∩ (C ∩ N)`. The proof applies
Mathlib's injection identity for the final-functor colimit isomorphism,
then the published finite-stage comparison identity.
`transferSourceComparisonIso_inv_ι` proves the corresponding inverse
identity by cancellation with the isomorphism.

This is a change of index for the source of the intended transfer.
It introduces no assumed comparison or transfer coherence: all
isomorphism certificates come from the two published constructions.
The finite-corestriction refinement proof is a separate prerequisite
for constructing the eventual map out of this source colimit.

The provenance is derived from Serre, *Local Fields*, Greenberg translation
(1979), Chapter X, Section 3, printed page 154 / PDF page 160:
open-normal fixed-coefficient stages and their inflation-indexed limit.
The normal-core indexing and the categorical composition are implementation
details, not quotations from Serre.
Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
