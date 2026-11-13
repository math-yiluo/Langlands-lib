# Unimodularity of the norm kernel `⁰G` (Renard V.2.3)

Author: Worker 103 (Task 5711, `8f1184cf-8c14-4ede-a502-96f1d8f66ec2`).

Module `Langlands.Representation.Plancherel.RationalNormKernelUnimodularProof`.
The theorem `Langlands.Plancherel.rationalNormKernelUnimodular` proves exactly the
published proposition
`Langlands.Plancherel.RationalNormKernelUnimodularStatement.{u}` (module
[`RationalNormKernelRemarksStatements`](RationalNormKernelRemarksStatements.md)).
It holds at every universe `u` and adds no hypotheses.

## Statement

Let `F : Type u` be a nonarchimedean local field, of any characteristic, and `G` a
connected reductive group scheme over `Spec F`. Give `G(F) = GroupScheme.rationalPoints G`
the canonical `rationalPointTopology`. Assume that `G(F)` is locally compact, Hausdorff
and a nonarchimedean group, as the statement's instance binders require. Then every
`h ∈ ⁰G = rationalCommonNormKernel G` has `MeasureTheory.Measure.modularCharacter h = 1`.
Here `⁰G` carries the subspace topology and the statement's local-compactness instance.

## Implemented proof

1. **Borel structures.** The proof equips `G(F)`, `⁰G`, the left quotient
   `QuotientIntegration.LeftQuotient ⁰G` and the quotient group `G(F) ⧸ ⁰G` with their
   Borel σ-algebras. Mathlib's `modularCharacter` does not depend on these choices.
   They are only the measurable-space parameters of the quotient-integration lemma used
   next.
2. **Restriction to a closed normal subgroup.** `⁰G` is closed
   (`isClosed_rationalCommonNormKernel`, module `RationalCharacterTopology`). It is normal
   by the instance `rationalCommonNormKernel_normal`. The published
   `QuotientIntegration.modularCharacter_normalSubgroup` (module
   [`NormalSubgroupModularCharacter`](../../Analysis/Local/NormalSubgroupModularCharacter.md))
   says that for a closed normal subgroup `H` of a locally compact Hausdorff group, the
   modular character of `H` at `h` equals the modular character of the ambient group at
   `h`. Hence `modularCharacter h = modularCharacter (h : G(F))`. The local-compactness
   instance on `⁰G` that this lemma uses comes from closedness, and the statement's comes
   from openness. `LocallyCompactSpace` is a proposition, so the two agree definitionally.
3. **Unimodularity of `G(F)`.** The published
   `Aubert.General.RationalPointFamily.rationalReductiveUnimodularity` (module
   [`RationalReductiveUnimodularityProof`](../Aubert/General/RationalReductiveUnimodularityProof.md))
   proves `RationalReductiveUnimodularityStatement`. That statement takes the standard
   cocharacter statement as an argument, which the proof supplies with the published
   `GroupScheme.standardCocharacter` (module
   [`StandardCocharacterProof`](../../GroupScheme/Rational/StandardCocharacterProof.md)).
   Then `modularCharacter (h : G(F)) = 1`.

The point type in `RationalReductiveUnimodularityStatement` is written
`RationalPoint F G.X` with `pointTopology`. It agrees definitionally with
`GroupScheme.rationalPoints G` and `rationalPointTopology F G.X`, so the term applies
without a transport.

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to the literature

David Renard, *Représentations des groupes réductifs p-adiques* (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), V.2.3, Proposition
(printed p.106 / PDF p.112). Renard's proof ends: « Comme `⁰G` contient des sous-groupes
ouverts compacts, il doit être ouvert dans `G`. Il est donc unimodulaire car `G` l'est. »
Renard deduces unimodularity from openness. The Lean proof uses closedness and normality
instead, through the modular character of a closed normal subgroup. Both routes rest on
the unimodularity of `G(F)`, which is Renard V.5.4 and is proved in the Library as
`rationalReductiveUnimodularity`.

## Scope

This proves only `RationalNormKernelUnimodularStatement`. The other two statements of the
module, `RationalNormKernelRestrictionStatement` and
`RationalNormKernelCompactCenterStatement`, are proved separately in
[`RationalNormKernelRestrictionProof`](RationalNormKernelRestrictionProof.md) and
[`RationalNormKernelCompactCenterProof`](RationalNormKernelCompactCenterProof.md).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements` | the target statement, `rationalCommonNormKernel`, `isClosed_rationalCommonNormKernel` (through its imports) |
| `Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof` | `rationalReductiveUnimodularity` |
| `Langlands.GroupScheme.Rational.StandardCocharacterProof` | `standardCocharacter` |
| `Langlands.Analysis.Local.NormalSubgroupModularCharacter` | `QuotientIntegration.modularCharacter_normalSubgroup` |
