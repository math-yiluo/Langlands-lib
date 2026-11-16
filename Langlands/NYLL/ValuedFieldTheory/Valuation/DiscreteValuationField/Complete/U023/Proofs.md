# A uniformizer of a complete DVF lies in the maximal ideal

This module proves the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.uniformizer_mem_maximalIdeal`, the proof phase of
M107.023 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m107).
Its type is the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.uniformizer_mem_maximalIdealStatement` applied to the
theorem's parameters:

```lean
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    uniformizer_mem_maximalIdealStatement F hpi
```

## Target and binders

The section variable is that of the published statement module and the source: `{K : Type u} [Field K]`, in `namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF` with `universe u v`. The theorem takes `F`, the implicit `{pi : F.valuationSubring}` and `hpi`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements`, the target is the proposition

```lean
pi ∈ F.maximalIdeal
```

Here `F : CompleteDVF.{u, v} K` (M107.006) is a field `K` with a chosen value group `F.ValueGroup`, a valuation `F.valuation : Valuation K F.ValueGroup` and an instance `Valuation.IsCompleteDiscrete F.valuation` (M107.001): the valuation is rank-one discrete (`IsRankOneDiscrete`, an instance through M107.001) and its valuation subring is complete for the adic topology of its maximal ideal; `F.valuationSubring` and `F.maximalIdeal` (M107.009, M107.010) are abbreviations, read along `F.toHenselianDVF` (M107.007) and its underlying DVF, that unfold to the valuation subring `F.valuation.valuationSubring` of `K`, as a type, and to its local-ring maximal ideal `IsLocalRing.maximalIdeal F.valuation.valuationSubring`; `pi : F.valuationSubring`; and `hpi` says that `F.valuation.IsUniformizer (pi : K)`, where `F.valuation.IsUniformizer (pi : K)` is Mathlib's predicate that the valuation of `pi` is the generator less than one of the cyclic value group of the rank-one discrete valuation. The target says that `pi` lies in the maximal ideal; it does not mention `hpi`, which is the hypothesis of the implication. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements`, which defines the target and, through the published `Complete.Projections`, `Complete.Definitions`, `Henselian.Definitions` and DVF modules, imports `IsCompleteDiscrete` (M107.001), `CompleteDVF` (M107.006) with its projections (M107.007–M107.012), and Mathlib's discrete valuations (`Mathlib.RingTheory.Valuation.Discrete.Basic`) and adic completeness.

The module opens no namespace, as the source does not.

## Implemented proof

After `show` states the published proposition unfolded, `change` rewrites the target as `pi ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring`, and the proof is `(Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one`: by Mathlib, an element of the valuation subring lies in its maximal ideal when its valuation is less than one, and a uniformizer has valuation less than one (`Valuation.IsUniformizer.val_lt_one`). The source proves the theorem by `F.toDVF.uniformizer_mem_maximalIdeal hpi`, that is M103.021 `DVF.uniformizer_mem_maximalIdeal`, whose source proof (`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, lines 155–160) is a `change` to `IsLocalRing.maximalIdeal F.valuation.valuationSubring` followed by `(Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one`. That DVF theorem is routed to Task `b7eca77b-bb19-49c0-baf5-8202858c322f` and is not in the Library, so the port uses its source body directly, unchanged except for writing the Mathlib namespace as `_root_.Valuation`. The original `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean` has SHA-256 `abda99fd0b28655e1317ae832e8c94c7431b7229d99cf07138d89c4a5c953493`. The port writes `_root_.Valuation` for Mathlib's namespace to make explicit that the Mathlib declaration is meant, since inside `Langlands.NYLL.ValuationTheory.DiscreteValuationField` the name `Valuation` also denotes the NYLL namespace of `IsCompleteDiscrete`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`, lines 205–209](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean#L205-L209):
the docstring at line 205 and the theorem at lines 206–209. It lies in `namespace ValuationTheory` (line 15), its `noncomputable section` (line 17), `universe u v w` (line 19), `namespace DiscreteValuationField` (line 21) and `namespace CompleteDVF` (line 112), with the variable `{K : Type u} [Field K]` (line 114). The source is:

```lean
/-- Every chosen uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal :=
  F.toDVF.uniformizer_mem_maximalIdeal hpi
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`;
its SHA-256 is `509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the published statement module;
- give the theorem the published proposition `uniformizer_mem_maximalIdealStatement F hpi` as its type, and begin the proof with `show` stating it unfolded;
- replace the source term `F.toDVF.uniformizer_mem_maximalIdeal hpi` (M103.021, unpublished) by its source body, writing Mathlib's namespace as `_root_.Valuation`;
- omit the universe `w` and all other source declarations.

The theorem's name, docstring and binders are the source's. The retained original belongs to registered source
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

This module proves only M107.023. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
