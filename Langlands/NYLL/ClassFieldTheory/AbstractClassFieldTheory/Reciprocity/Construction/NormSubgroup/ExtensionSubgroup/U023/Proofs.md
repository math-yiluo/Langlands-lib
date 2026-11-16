# The subgroup of the maximal unramified field is normal

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_maximalUnramifiedField_normal`, the proof phase of
M029.023 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m029).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_maximalUnramifiedField_normalStatement` applied to the
theorem's parameters:

```lean
theorem extensionSubgroup_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    extensionSubgroup_maximalUnramifiedField_normalStatement D K L hLK
```

## Target and binders

The section variables are those of the published statement module and the source: `universe u` and `{G : Type u} [Group G] [TopologicalSpace G]` in `section maximalUnramifiedFields`, `namespace DegreeData`. The theorem takes `D`, `K`, `L`, `hLK` and the instance binder `[hLnormal : (extensionSubgroup K L hLK).Normal]`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.ExtensionSubgroup.Statements`, the target is the proposition

```lean
(extensionSubgroup K (D.maximalUnramifiedField L)
  ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
    inf_le_left).trans hLK)).Normal
```

Here `D : DegreeData G` (M010.002) is a degree datum (a continuous homomorphism `D.degree` from `G` to the profinite integers written multiplicatively), `K L` are closed subgroups (abstract fields) and `hLK : L ≤ K`. `D.maximalUnramifiedField L` (M029.016) is the maximal unramified extension `\widetilde L` of `L`, represented by the closed subgroup `D.fieldInertia L` (M010.012), which is `L ⊓ D.inertia`, the elements of `L` of degree `1`. `extensionSubgroup K M hMK` (M004.002, discharged as Mathlib's `Subgroup.subgroupOf`) is a subgroup `M ≤ K` regarded as a subgroup of `K`; the containment proof `(show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from inf_le_left).trans hLK` is the source proof of M029.020 `maximalUnramifiedField_le_of_le hLK`. `D.extensionInertiaWithin K L hLK` (M012.002) is the relative inertia subgroup `L ∩ I_K` inside `K`, where `I_K = D.fieldInertiaWithin K` (M010.014) is the kernel of the degree on `K`. The instance binder `hLnormal` says that the subgroup of `L` is normal in `K`. The target says that the subgroup of `\widetilde L` is then normal in `K`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.ExtensionSubgroup.Statements`, which defines the target and imports `maximalUnramifiedField` (M029.016), `extensionInertiaWithin` (M012.002) with its normality instance `extensionInertiaWithin_normal` (M012.003), `fieldInertia` (M010.012), `fieldInertiaWithin` (M010.014) and `extensionSubgroup` (M004.002);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U013.Proofs`, the published proof of M010.013 `DegreeData.mem_fieldInertia_iff` (`g ∈ D.fieldInertia L ↔ g ∈ L ∧ D.degree g = 1`);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U016.Proofs`, the published proof of M010.016 `DegreeData.mem_fieldInertiaWithin_iff` (`k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1`);
- `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs`, the published proof of M022.001 `KummerTheory.mem_extensionSubgroup_iff` (`k ∈ extensionSubgroup K M hMK ↔ (k : G) ∈ M`).

The module opens `CyclicCohomology`, as the source does; the source's `open KummerTheory` is omitted, since the only name it would supply, `mem_extensionSubgroup_iff`, is written with its full namespace.

## Implemented proof

The source proof rewrites the subgroup with M029.022 `D.extensionSubgroup_maximalUnramifiedField K L hLK`, whose proof is not yet in the Library, and closes the goal with `infer_instance`. The module proves M029.022 as the private theorem `extensionSubgroup_maximalUnramifiedField_aux`, with the published proposition's unfolded statement (the target's containment proof in place of `D.maximalUnramifiedField_le_of_le hLK`) and the source proof of M029.022, adapted as in the proof module of M029.022: the source proof applies three membership criteria: M022.001 `mem_extensionSubgroup_iff` and M010.016 `mem_fieldInertiaWithin_iff`, which are published with `...Statement` types, and M029.018 `mem_maximalUnramifiedField_iff` (`g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1`), whose proof is not yet in the Library. The module first states local facts `hmemExt`, `hmemMax` and `hmemIn` with the unfolded statements of these three criteria; `hmemExt` and `hmemIn` are the published theorems, and `hmemMax` is the published M010.013 `mem_fieldInertia_iff`, which is the source proof of M029.018 after its rewrite with M029.017 `maximalUnramifiedField_eq_fieldInertia`, a `rfl` theorem (the maximal unramified field is by definition `D.fieldInertia L`). The rest is the source proof with these facts in place of the three theorems, and with the target's containment proof in place of `D.maximalUnramifiedField_le_of_le hLK` (the same proof by proof irrelevance): by `ext k`, an element `k` of `K` lies in the subgroup of `\widetilde L` iff `k ∈ \widetilde L` (`hmemExt`), iff `k ∈ L` and `D.degree k = 1` (`hmemMax`), iff `k` lies in the subgroup of `L` (`hmemExt` for `L`) and in `I_K` (`hmemIn`), which is membership in `D.extensionInertiaWithin K L hLK`.

The main proof unfolds the published proposition, rewrites with `extensionSubgroup_maximalUnramifiedField_aux D K L hLK` and closes the goal `(D.extensionInertiaWithin K L hLK).Normal` by `infer_instance`, which finds the published instance M012.003 `extensionInertiaWithin_normal` (whose hypotheses include the normality of the subgroup of `L`, the binder `hLnormal`). The development check reported only the axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passages are
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`, lines 210–225](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean#L210-L225) and [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`, lines 249–279](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean#L249-L279):
the theorems M029.017 and M029.018 with their docstrings at lines 210–225, the theorem M029.022 with its docstring at lines 249–270, and the docstring at line 272 and the theorem at lines 273–279. They lie after `universe u` (line 18) in `namespace ClassFormation` (line 20), with `open KummerTheory` (line 22) and `open CyclicCohomology` (line 24), its `noncomputable section` (line 28), `section maximalUnramifiedFields` (line 198) with `variable {G : Type u} [Group G] [TopologicalSpace G]` (line 200) and `namespace DegreeData` (line 202). The source passages are:

```lean
/-- The implementation theorem identifying the maximal unramified field
with absolute inertia.  Downstream code should use this theorem instead of
unfolding `maximalUnramifiedField`. -/
theorem maximalUnramifiedField_eq_fieldInertia
    (D : DegreeData G) (L : ClosedSubgroup G) :
    D.maximalUnramifiedField L = D.fieldInertia L := by
  rfl

/-- Membership in the maximal unramified field is the expected inertia
condition. -/
@[simp]
theorem mem_maximalUnramifiedField_iff
    (D : DegreeData G) (L : ClosedSubgroup G) (g : G) :
    g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1 := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact D.mem_fieldInertia_iff L g
```

```lean
/-- Inside `G_K`, the absolute subgroup of `\widetilde L` is the relative
inertia subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) =
      D.extensionInertiaWithin K L hLK := by
  ext k
  constructor
  · intro hk
    have hkMax : k.1 ∈ D.maximalUnramifiedField L :=
      (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) k).1 hk
    have hkData := (D.mem_maximalUnramifiedField_iff L k.1).1 hkMax
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).2 hkData.1,
      (D.mem_fieldInertiaWithin_iff K k).2 hkData.2⟩
  · intro hk
    apply (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK) k).2
    apply (D.mem_maximalUnramifiedField_iff L k.1).2
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).1 hk.1,
      (D.mem_fieldInertiaWithin_iff K k).1 hk.2⟩

/-- The subgroup representing the maximal unramified field is normal in the base subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK)).Normal := by
  rw [D.extensionSubgroup_maximalUnramifiedField K L hLK]
  infer_instance
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`;
its SHA-256 is `7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `extensionSubgroup_maximalUnramifiedField_normalStatement D K L hLK` as its type, and begin the proof with `unfold` of it;
- prove M029.022 as the private theorem `extensionSubgroup_maximalUnramifiedField_aux` by its source proof, with the local facts `hmemExt`, `hmemMax` and `hmemIn` in place of the three membership criteria, and rewrite with it in place of `D.extensionSubgroup_maximalUnramifiedField K L hLK`;
- omit `open KummerTheory` and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
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
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M029.023. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
