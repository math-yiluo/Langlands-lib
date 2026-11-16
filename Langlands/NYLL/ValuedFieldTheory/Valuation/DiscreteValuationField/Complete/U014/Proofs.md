# Adic completeness of the valuation subring of a complete DVF

This module proves the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.isAdicComplete`, the proof phase of
M107.014 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m107).
Its type is the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.isAdicCompleteStatement` applied to the
theorem's parameters:

```lean
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    isAdicCompleteStatement F
```

## Target and binders

The section variable is that of the published statement module and the source: `{K : Type u} [Field K]`, in `namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF` with `universe u v`. The theorem takes `F`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements`, the target is the proposition

```lean
IsAdicComplete F.maximalIdeal F.valuationSubring
```

Here `F : CompleteDVF.{u, v} K` (M107.006) is a field `K` with a chosen value group `F.ValueGroup`, a valuation `F.valuation : Valuation K F.ValueGroup` and an instance `Valuation.IsCompleteDiscrete F.valuation` (M107.001): the valuation is rank-one discrete (`IsRankOneDiscrete`, an instance through M107.001) and its valuation subring is complete for the adic topology of its maximal ideal; and `F.valuationSubring` and `F.maximalIdeal` (M107.009, M107.010) are abbreviations, read along `F.toHenselianDVF` (M107.007) and its underlying DVF, that unfold to the valuation subring `F.valuation.valuationSubring` of `K`, as a type, and to its local-ring maximal ideal `IsLocalRing.maximalIdeal F.valuation.valuationSubring`. The target says that the valuation subring is complete for the adic topology of its maximal ideal. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements`, which defines the target and, through the published `Complete.Projections`, `Complete.Definitions`, `Henselian.Definitions` and DVF modules, imports `IsCompleteDiscrete` (M107.001), `CompleteDVF` (M107.006) with its projections (M107.007–M107.012), and Mathlib's discrete valuations (`Mathlib.RingTheory.Valuation.Discrete.Basic`) and adic completeness.

The module opens no namespace, as the source does not.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof: `change` rewrites the target as adic completeness of `F.valuation.valuationSubring` for `IsLocalRing.maximalIdeal F.valuation.valuationSubring`, which is the field `isAdicComplete` of the instance `Valuation.IsCompleteDiscrete F.valuation` (M107.001) carried by `F`. The source closes it with `Valuation.isAdicComplete F.valuation` (M107.002, whose source proof is that field); M107.002 is proved by a sibling candidate of this task and is not yet in the Library, so the port uses its body `Valuation.IsCompleteDiscrete.isAdicComplete (val := F.valuation)` directly, and the module can be staged independently of M107.002.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`, lines 154–160](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean#L154-L160):
the docstring at line 154 and the theorem at lines 155–160. It lies in `namespace ValuationTheory` (line 15), its `noncomputable section` (line 17), `universe u v w` (line 19), `namespace DiscreteValuationField` (line 21) and `namespace CompleteDVF` (line 112), with the variable `{K : Type u} [Field K]` (line 114). The source is:

```lean
/-- The complete DVR model is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring := by
  change IsAdicComplete
    (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    F.valuation.valuationSubring
  exact Valuation.isAdicComplete F.valuation
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`;
its SHA-256 is `509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the published statement module;
- give the theorem the published proposition `isAdicCompleteStatement F` as its type, and begin the proof with `show` stating it unfolded;
- replace the source term `Valuation.isAdicComplete F.valuation` (M107.002, not yet published) by its source body `Valuation.IsCompleteDiscrete.isAdicComplete (val := F.valuation)`;
- omit the universe `w` and all other source declarations.

The theorem's name, docstring, binders and `change` step are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

Worker 5264 wrote the Lean file and, apart from this paragraph, this Markdown as
revision 1 of the public draft of Task 7144
(`a514e7ad-f1fb-42b8-9ac0-1e7f9df3acc4`) and is credited as coauthor.
Worker 741 staged it with the Lean file unchanged, after recompiling it on
16 November 2026 in the approved environment (no errors or warnings; the theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`).

This module proves only M107.014. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
