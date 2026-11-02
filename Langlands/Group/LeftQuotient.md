# Shared left-coset constructions

This module collects the existing generic quotient declarations from
[Induction/Definitions](../Representation/Induction/Definitions.md),
[QuotientMeasure](../Analysis/Local/QuotientMeasure.md), and
[QuotientTopology](../Analysis/Local/QuotientTopology.md). Their public names,
parameters, representative formulas and proofs are retained. The carrier
`Langlands.QuotientIntegration.LeftQuotient` transparently reuses
`Langlands.Induction.LeftQuotient`; both are the actual right-relation quotient.

Worker 15 supplied the induction carrier, projection and positive translation;
Worker 31 supplied invariant-function descent and the translation homeomorphism.
`descend` retains arbitrary Sort-valued codomains. Right translation sends the
class of `x` to the class of `x * g`; its inverse is translation by `g⁻¹`.
These elementary constructions require no representation or integration imports.

Worker 113 proves topological prerequisites for quotient integration on the
published `Langlands.QuotientIntegration.LeftQuotient H`, whose cosets are `H g`.
The existing quotient and its topology are unchanged. The abbreviation
`leftQuotientMap H` reuses `Langlands.Induction.quotientMap H` from
this shared module: it sends `g` to the class
of `g` under `QuotientGroup.rightRel H`. This retains the analysis interface
without a second implementation of the projection. The representative formula
is definitional. The accompanying lemmas supply the topological API required
for compactly supported averaging on this actual quotient.

This is an internal derivation from pinned Mathlib. In
`Mathlib/GroupTheory/Coset/Defs.lean`, `QuotientGroup.rightRel H` is defined as
`MulAction.orbitRel H G` for the subgroup's left multiplication action. Thus
`MulAction.isOpenQuotientMap_quotientMk` applies directly to the published
quotient projection. Its `locallyCompactSpace` consequence proves local
compactness when the ambient group is locally compact.

For a closed subgroup, Mathlib's proper-action instances first show that the
ambient group's action on itself is proper, then restrict it along the closed
subgroup embedding. The theorem
`t2Space_quotient_mulAction_of_properSMul` consequently proves Hausdorffness
of the same orbit space. These facts come from
`Mathlib/Topology/Algebra/ProperAction/Basic.lean`.

No normality, countability, Haar measure or quotient-measure existence is
assumed. Ambient Hausdorffness is not needed for these topological lemmas;
they apply in particular under the locally compact Hausdorff hypotheses of
the compatible-measure existence task. They do not construct a measure.

The original modules re-export these declarations. The general adelic
[LeftCosetSpace](../Global/LeftCosetSpace.md) interface reuses them for its
carrier, projection, translation, descent and topological instances.
