# The Frobenius fixed field is finite

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_finite`, the proof phase of
M016.010 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m016).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_finiteStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusFixedField_finiteStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type*} [Group G] [TopologicalSpace G]`, then `D : DegreeData G` (M010.002), `[IsTopologicalGroup G] [CompactSpace G] [T2Space G]`, `K : FiniteResidueAbstractField D` (M010.021), a closed subgroup `L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instances `hLnormal` and `hLfinite`, and a Frobenius lift `σ : D.FrobeniusElements K L hLK` (M012.009). The source writes the normality instance and the finiteness instance with `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body. The source conclusion is written with `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)`, whose body is the subgroup in the published target.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, the target is the proposition

```lean
Finite
  (K.field.toSubgroup ⧸
    (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup)
```

That is, the Frobenius fixed field `Σ = frobeniusFixedField K L hLK σ` (M016.004) is a finite extension of `K`: `G_Σ`, read inside `G_K`, has finite index. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`, which defines the target and imports the published definitions `frobeniusFixedSubgroupWithin` (M016.001), `frobeniusFixedField` (M016.004), `frobeniusClosure` (M014.023) and `extensionInertiaWithin` (M012.002);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.U039.Proofs`, the proof of M014.039 `frobeniusFixedField_finiteIndex` in this task.

The module opens no namespace.

## Implemented proof

After `show` unfolds the target, the proof follows the source. With `N = I_L`, `Q = G_K ⧸ N` and `Γ` the Frobenius closure, M014.039 (stated first as the local fact `hfin`, since its type is a Statement proposition) makes `Q ⧸ Γ` finite, so `Γ` has nonzero index; the subgroup `S = frobeniusFixedSubgroupWithin K L hLK σ` is by definition the preimage of `Γ` under the surjection `G_K → Q`, so `S` has the same nonzero index. The source then rewrites the subgroup of the target with M016.007 `extensionSubgroup_frobeniusFixedField`, whose proof is not in the Library; the module proves that equation as the local fact `hSeq` by its source proof (`ext`, then both directions of the membership characterization), in which the source's rewrite with M016.005 `mem_frobeniusFixedField_iff` (proved by `rfl` in the source) is folded into the preceding `change`. Rewriting with `hSeq` turns the goal into the nonzero index of `S`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`, lines 168–200](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean#L168-L200):
the docstring at line 168 and the theorem at lines 169–200. It lies in `namespace ClassFormation` (line 17), with `open CyclicCohomology` (line 19), its `noncomputable section` (line 23), the variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 25) and `namespace DegreeData` (line 27). The inlined M016.007 is at lines 112–133 and M016.005 at lines 87–98 of the same file. The source is:

```lean
/-- finiteness of the Frobenius fixed field on the actual field side: `Σ | K` is finite. -/
theorem frobeniusFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) := by
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ, N] using
      D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓ : Γ.index ≠ 0 := Γ.index_ne_zero_of_finite
  have hS : S.index ≠ 0 := by
    rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
    rw [Subgroup.index_comap_of_surjective Γ
      (QuotientGroup.mk'_surjective N)]
    exact hΓ
  apply Nat.finite_of_card_ne_zero
  change
    (extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ)).index ≠ 0
  rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
  exact hS
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`;
its SHA-256 is `707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.

Modifications by Worker 5264 on 15 November 2026:

- give the theorem the published proposition `frobeniusFixedField_finiteStatement D K L hLK σ` as its type, unfolded by an initial `show`;
- state the published M014.039, whose type is its Statement proposition, as the local fact `hfin` before the source's `simpa`;
- replace `rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]` (M016.007, not proved in the Library) by the local equation `hSeq`, proved by M016.007's source proof with its `change` and `rw [D.mem_frobeniusFixedField_iff K L hLK σ]` merged into one `change` to the unfolded membership, and `rw [hSeq]`, with a comment;
- expand `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)` in the source `change` to its abbreviation body; the expanded form needs no inclusion proof, so M016.006 `frobeniusFixedField_le` is not used;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` in the normality and finiteness binders to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology`, the `noncomputable section` and all other source declarations; keep the variable line.

The docstring, the binders and all other proof steps are the source's. The retained original belongs to registered source
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

This module proves only M016.010. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
