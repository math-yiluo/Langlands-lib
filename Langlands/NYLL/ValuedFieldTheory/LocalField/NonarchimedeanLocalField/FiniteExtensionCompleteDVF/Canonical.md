# The canonical complete discrete valuation of a nonarchimedean local field

This module adapts exactly M248.001, `LocalFieldTheory.localCompleteDVF`, from
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`, lines 34–55](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L34-L55),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its adapted name is `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`.
It is a noncomputable structural definition: it packages data and proofs into a
`CompleteDVF` and states no theorem.

## Parameters and result

The definition has the single universe level `u`. Its complete parameter
telescope is that of the source:
`(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`.
The result is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,u} K`.

Here `K` is an arbitrary field in an arbitrary universe, with its supplied
valuative relation and supplied topology. Mathlib's
`IsNonarchimedeanLocalField K` requires that this topology be the valuative
topology, that `K` be locally compact, and that the valuative relation be
nontrivial. The definition adds no premise. In particular it takes no
`UniformSpace`, `CompleteSpace`, rank-one-discreteness, `IsAdicComplete` or
finite-extension hypothesis, and it declares no global instance. It concerns
the canonical valuation of `K` itself, not a valuation chosen on an extension,
and it is not specialised to `p`-adic fields or to `Type 0`.

The returned bundle has these fields:

| Field | Stored data |
| --- | --- |
| `ValueGroup` | Exactly `ValuativeRel.ValueGroupWithZero K`, the canonical value group of the valuative relation. |
| `instValueGroup` | Mathlib's canonical `LinearOrderedCommGroupWithZero` instance on `ValuativeRel.ValueGroupWithZero K`. |
| `valuation` | `Valued.v` for Mathlib's `Valued K (ValuativeRel.ValueGroupWithZero K)` instance, which is definitionally the canonical valuation `ValuativeRel.valuation K`. |
| `instCompleteDiscrete` | The published `Valuation.IsCompleteDiscrete` proof for this valuation: rank-one discreteness, and adic completeness of its valuation subring at its maximal ideal. |

## Construction

The implemented definition follows the source construction. Its steps are:

1. **Compatible uniformity.** Locally put
   `UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K` and
   `IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup`. The right
   uniformity of the topological additive group `K` has the supplied topology
   as its underlying topology, by definition. The definition therefore keeps
   the original topology. Because `K` is commutative, this uniformity makes
   `K` a uniform additive group.
2. **Canonical valuation.** With this uniformity, Mathlib's low-priority
   instance `Valued K (ValuativeRel.ValueGroupWithZero K)`
   (`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`) has
   `Valued.v := ValuativeRel.valuation K`. The local name
   `v : Valuation K (ValuativeRel.ValueGroupWithZero K) := Valued.v` is bound
   with `letI`, so it is inlined and leaves no binding in the term.
3. **Nontriviality.** `IsNonarchimedeanLocalField K` contains
   `ValuativeRel.IsNontrivial K`. Mathlib's instance in
   `Mathlib/NumberTheory/LocalField/Basic.lean` shows that `Valued.v` is
   compatible with the valuative relation, so
   `ValuativeRel.isNontrivial_iff_isNontrivial v` gives `v.IsNontrivial`.
   Mathlib then infers that the value group
   `MonoidWithZeroHom.valueGroup (.ofClass v)` is nontrivial.
4. **Cyclicity.** Mathlib's local-field file proves the instance
   `IsCyclic (ValuativeRel.ValueGroupWithZero K)ˣ`. The value group of `v` is
   a subgroup of these units, so `Subgroup.isCyclic_of_le le_top` makes it
   cyclic.
5. **Rank-one discreteness.** Mathlib's `Valuation.IsRankOneDiscrete.mk' v`
   turns the cyclic, nontrivial value group into `v.IsRankOneDiscrete`.
6. **Completeness and packaging.** Mathlib's instance `CompleteSpace K` in
   `Mathlib/NumberTheory/LocalField/Basic.lean` applies to any uniformity
   `[UniformSpace K] [IsUniformAddGroup K]` compatible with
   `IsNonarchimedeanLocalField K`. In particular it applies to the uniformity
   from step 1. The published
   `Langlands.NYLL.ValuationTheory.Valuations.completeDVFOfCompleteValuedField`
   is then applied with value group `ValuativeRel.ValueGroupWithZero K`, the
   `Valued` instance of step 2, the instance of step 5 and this completeness.
   It sets `ValueGroup := ValuativeRel.ValueGroupWithZero K` and
   `valuation := Valued.v`. Its completeness field contains the actual
   maximal-ideal adic completeness of the valuation subring, proved by the
   published `rankOneDiscreteValuationSubring_isAdicComplete`.

All instances above stay local to the definition. After elaboration, the
definition's body is
`fun K _ _ _ _ => Langlands.NYLL.ValuationTheory.Valuations.completeDVFOfCompleteValuedField`.
The constructor's instance arguments are the terms described in steps 1–6.

## Reuse and imports

The two direct imports are:

- `Mathlib.NumberTheory.LocalField.Basic`, supplying
  `IsNonarchimedeanLocalField`, the cyclic unit-group, compatibility and
  `CompleteSpace` instances above, and, through its imports, the valuative
  `Valued` instance, the right uniformity and the discrete-valuation API.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteDVF`,
  the published M247.004 module supplying `completeDVFOfCompleteValuedField`
  and, through its imports, `CompleteDVF`.

The original file imports the NYLL modules
`NonarchimedeanLocalField.Basic`,
`DiscreteValuationField.FiniteIntegralClosure` and `ValuedAdicComplete`, and
also `Mathlib.Algebra.Order.Hom.Units`. M248.001 needs none of these beyond
the constructor. `FiniteIntegralClosure` serves the chosen-extension part of
the original file. `Mathlib.Algebra.Order.Hom.Units` was needed only for the
cyclicity transport that this adaptation omits. No external NYLL repository
module is imported.

## Differences from the source

- The source proves `IsCyclic (ValuativeRel.ValueGroupWithZero K)ˣ` itself, by
  transporting cyclicity along
  `(OrderMonoidIso.unitsCongr (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).trans OrderMonoidIso.unitsWithZero`.
  Current Mathlib proves the same instance in
  `Mathlib/NumberTheory/LocalField/Basic.lean` by a transport along
  `valueGroupWithZeroIsoInt K`. This adaptation uses that instance and omits
  the local transport. The instance is a `Prop`, so the resulting data are
  unchanged.
- The source writes the value group as
  `MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom`. In the pinned Mathlib,
  `Valuation.IsRankOneDiscrete.mk'` is stated for
  `MonoidWithZeroHom.valueGroup (.ofClass v)`, and the adaptation uses that
  spelling. The `show … ≤ ⊤` type ascription before `le_top` is unnecessary
  and has been dropped.
- The source binds `v` with `let`; the adaptation uses `letI`, which yields the
  same constructor application without a leftover local binding.
- The namespace is prefixed with `Langlands.NYLL`, and `Valuation` is written
  `_root_.Valuation` because of the `Langlands.NYLL.ValuationTheory`
  namespace. The source opens
  `ValuationTheory.DiscreteValuationField.ValuedExtension` and
  `scoped ValuativeRel`, which this definition does not use; they are omitted.
  The source universes `v` and `y` belong to other units in the same file.

Only M248.001 is adapted. The later results of the same file belong to
separate units: extension compatibility, comparison of rings of integers,
finite-module theorems, chosen extension data and instances, and uniqueness.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a definition with the single level parameter
`u`. It depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. A separate private check module printed the complete unapplied
definition and its type, displaying exactly the telescope and the
`CompleteDVF.{u,u} K` result above. It verified by `rfl` that:

- `(localCompleteDVF K).ValueGroup = ValuativeRel.ValueGroupWithZero K`;
- `(localCompleteDVF K).instValueGroup` is the canonical instance;
- `(localCompleteDVF K).valuation` is both `ValuativeRel.valuation K` and
  `Valued.v` under the right uniformity;
- the right uniformity's underlying topology is the supplied topology.

Under that uniformity, `CompleteSpace K` was also found by instance inference.
These checks establish compilation and the data correspondence stated here.
Semantic review and publication are separate steps.

## Attribution and modifications

The complete 206-line original was read. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The workspace, project notes and Library used for this adaptation contain no
source-specific errata directory.

The original copyright and author header is retained verbatim. The inherited,
unmodified [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values
are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE has no entry for the selected source file. The
third-party source table `Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` in
the supplement does not list it either. The supplement's
`.github/verification/publication.json` records the SHA256 given above.

On 30 October 2026, Worker 785 extracted the single definition and made the
namespace, import and API changes listed above. Worker 785 also wrote this
explanation. Worker 106 supplied routing only. No unpublished implementation
or draft from another worker was reused.
