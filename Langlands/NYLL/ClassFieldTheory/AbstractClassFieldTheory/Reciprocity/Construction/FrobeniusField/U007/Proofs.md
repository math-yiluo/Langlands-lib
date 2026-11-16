# The subgroup of the Frobenius fixed field inside the base

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_frobeniusFixedField`, the proof phase of
M016.007 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m016).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_frobeniusFixedFieldStatement` applied to the
theorem's parameters:

```lean
theorem extensionSubgroup_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    extensionSubgroup_frobeniusFixedFieldStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type*} [Group G] [TopologicalSpace G]` (the ambient group with its group structure and topology), then the explicit parameter `D : DegreeData G` (M010.002, the degree datum: a continuous surjective degree homomorphism `G → ℤ̂`), the instance argument `[IsTopologicalGroup G]`, `K : FiniteResidueAbstractField D` (M010.021, an abstract field with finite residue degree), `L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.field.toSubgroup` (an abstract extension `L` of `K`), the instance argument `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` (normality of `L` in `K`) and `σ : D.FrobeniusElements K L hLK` (a Frobenius lift, M012.009: a class `σ` in `G(\widetilde L|K) = K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` together with the property that its normalized degree `D.extensionNormalizedDegree K L hLK σ` (M012.005) is `(Multiplicative.ofAdd (1 : ZHat)) ^ n` for some natural number `n > 0`). The source writes the subgroup in `hLnormal` as `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, the target is the proposition

```lean
(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup =
  D.frobeniusFixedSubgroupWithin K L hLK σ
```

That is, the subgroup of `G_K = K.field.toSubgroup` cut out by the Frobenius fixed field `Σ` (M016.004) is exactly `frobeniusFixedSubgroupWithin` (M016.001). The source writes the left-hand side as `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)`; the abbreviation body `Subgroup.subgroupOf` does not use the inclusion proof `frobeniusFixedField_le` (M016.006), so it does not occur in the target. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, which defines the target and imports, through the sibling `Definitions` module, the published definitions `frobeniusClosure` (M014.023: the closed subgroup `Γ = closure ⟨σ⟩` of `G(\widetilde L|K)`), `extensionInertiaWithin` (M012.002) and `frobeniusFixedSubgroupWithin` (M016.001: the inverse image of `Γ` under `QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)`), and `frobeniusFixedField` (M016.004: the closed subgroup of `G` whose underlying subgroup is the image of `frobeniusFixedSubgroupWithin` under the inclusion `K.field.toSubgroup.subtype`).

The module opens no namespace.

## Implemented proof

The proof unfolds the target with `show` and then follows the source. After `ext k` for `k : K.field.toSubgroup`, the first `change` (from the source) states membership on the left as `k.1 ∈ D.frobeniusFixedField K L hLK σ`. The source then rewrites with its `rfl` lemma `mem_frobeniusFixedField_iff` (M016.005); the published M016.005 is a Statement, so the implemented proof instead uses a second `change` to the right-hand side of that equivalence, `∃ t, t ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ t.1 = k.1`, which holds definitionally. For the forward direction, a witness `t` with `t.1 = k.1` equals `k` by `Subtype.ext`, and `simpa [this] using ht` transports the membership. For the reverse direction, `k` itself is the witness.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`, lines 110–133](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean#L110-L133):
the docstring at lines 110–111 and the theorem at lines 112–133. It lies in `namespace ClassFormation` (line 17), with `open CyclicCohomology` (line 19), its `noncomputable section` (line 23), the group variables of line 25 and `namespace DegreeData` (line 27). The source is:

```lean
/-- Inside `G_K`, the subgroup attached to the actual field `Σ` is
literally the quotient-projection inverse image used in its definition. -/
theorem extensionSubgroup_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) =
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  ext k
  change
    (k.1 ∈ D.frobeniusFixedField K L hLK σ) ↔
      k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
  rw [D.mem_frobeniusFixedField_iff K L hLK σ]
  constructor
  · rintro ⟨t, ht, htk⟩
    have : t = k := by
      apply Subtype.ext
      exact htk
    simpa [this] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`;
its SHA-256 is `707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.

Modifications by Worker 752 on 16 November 2026, adapting the draft by Worker 5264 of 15 November 2026:

- give the theorem the published proposition `extensionSubgroup_frobeniusFixedFieldStatement D K L hLK σ` as its type and unfold it with an initial `show`;
- replace the source rewrite `rw [D.mem_frobeniusFixedField_iff K L hLK σ]` (line 125) by a `change` to the right-hand side of that `rfl` lemma (M016.005);
- in the statement, `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)` is expanded to `(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup`, which drops the unused proof argument M016.006;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology` (only needed for the abbreviation), the `noncomputable section` and all other source declarations.

The theorem name, its binders, the source variable declaration, its docstring and the other source proof steps are kept. The retained original belongs to registered source
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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M016.007. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
