# Membership in the Frobenius fixed field

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.mem_frobeniusFixedField_iff`, the proof phase of
M016.005 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m016).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.mem_frobeniusFixedField_iffStatement` applied to the
theorem's parameters:

```lean
theorem mem_frobeniusFixedField_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) :
    mem_frobeniusFixedField_iffStatement D K L hLK σ g
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type*} [Group G] [TopologicalSpace G]` (the ambient group with its group structure and topology), then the explicit parameter `D : DegreeData G` (M010.002, the degree datum: a continuous surjective degree homomorphism `G → ℤ̂`), the instance argument `[IsTopologicalGroup G]`, `K : FiniteResidueAbstractField D` (M010.021, an abstract field with finite residue degree), `L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.field.toSubgroup` (an abstract extension `L` of `K`), the instance argument `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` (normality of `L` in `K`) and `σ : D.FrobeniusElements K L hLK` (a Frobenius lift, M012.009: a class `σ` in `G(\widetilde L|K) = K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` together with the property that its normalized degree `D.extensionNormalizedDegree K L hLK σ` (M012.005) is `(Multiplicative.ofAdd (1 : ZHat)) ^ n` for some natural number `n > 0`), followed by the element `g : G`. The source writes the subgroup in `hLnormal` as `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, the target is the proposition

```lean
g ∈ D.frobeniusFixedField K L hLK σ ↔
  ∃ k : K.field.toSubgroup,
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g
```

That is, an element `g` of `G` lies in the Frobenius fixed field `frobeniusFixedField` (M016.004) exactly when it is the underlying element of some `k` in `frobeniusFixedSubgroupWithin` (M016.001). No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, which defines the target and imports, through the sibling `Definitions` module, the published definitions `frobeniusClosure` (M014.023: the closed subgroup `Γ = closure ⟨σ⟩` of `G(\widetilde L|K)`), `extensionInertiaWithin` (M012.002) and `frobeniusFixedSubgroupWithin` (M016.001: the inverse image of `Γ` under `QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)`), and `frobeniusFixedField` (M016.004: the closed subgroup of `G` whose underlying subgroup is the image of `frobeniusFixedSubgroupWithin` under the inclusion `K.field.toSubgroup.subtype`).

The module opens no namespace.

## Implemented proof

The proof unfolds the target with `show` and closes it with `exact Iff.rfl`. By its definition (M016.004), membership in `frobeniusFixedField` is membership in the image `Subgroup.map K.field.toSubgroup.subtype (D.frobeniusFixedSubgroupWithin K L hLK σ)`, which unfolds definitionally to the existence of a preimage `k` in the subgroup with `k.1 = g`. The source proves the equivalence by `rfl`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`, lines 87–98](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean#L87-L98):
the docstring at line 87, the attribute at line 88 and the theorem at lines 89–98. It lies in `namespace ClassFormation` (line 17), with `open CyclicCohomology` (line 19), its `noncomputable section` (line 23), the group variables of line 25 and `namespace DegreeData` (line 27). The source is:

```lean
/-- An element lies in the Frobenius fixed field exactly when Frobenius fixes its restriction. -/
@[simp]
theorem mem_frobeniusFixedField_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) :
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g := by
  rfl
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`;
its SHA-256 is `707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.

Modifications by Worker 752 on 16 November 2026, adapting the draft by Worker 5264 of 15 November 2026:

- give the theorem the published proposition `mem_frobeniusFixedField_iffStatement D K L hLK σ g` as its type and unfold it with an initial `show`, followed by `exact Iff.rfl` in place of the source tactic `rfl`;
- omit the source `@[simp]` attribute (line 88), since the theorem's type is now a Statement constant;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology` (only needed for the abbreviation), the `noncomputable section` and all other source declarations.

The theorem name, its binders, the source variable declaration and its docstring are kept. The retained original belongs to registered source
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

This module proves only M016.005. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
