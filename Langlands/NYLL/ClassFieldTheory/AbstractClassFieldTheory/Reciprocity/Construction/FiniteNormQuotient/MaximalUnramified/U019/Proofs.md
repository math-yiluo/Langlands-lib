# The maximal-unramified norm subgroup lies in a finite norm subgroup

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup`, the proof phase of
M039.019 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m039).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement` applied to the
theorem's parameters:

```lean
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement D A K L hLK
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (the universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires) in `section quotientMaps`. The theorem takes `D`, `A`, `K`, `L`, `hLK` and the instance binder `[hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, as the published target; the source writes `extensionSubgroup K L hLK`, whose body is this `Subgroup.subgroupOf`, as the published statement module records.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.Statements`, the target is the proposition

```lean
D.maximalUnramifiedNormSubgroup A K L ≤
  finiteNormSubgroup A K L hLK
```

Here `D : DegreeData G` (M010.002) is a degree datum, `A : Rep ℤ G` an integral representation, and `K L` closed subgroups (abstract fields) with `hLK : L ≤ K`, `L` of finite index in `K` (the instance binder `hfinite`). `finiteNormSubgroup A K L hLK` (M039.001) is the norm subgroup `N_{L|K} A_L`, the range of the relative norm from `A_L` to `A_K`. `D.maximalUnramifiedNormSubgroup A K L` (M029.024) is by definition `infiniteNormSubgroup A (D.maximalUnramifiedField L) K`, the intersection of the norm subgroups `N_{F|K} A_F` over all finite intermediate fields `F` of `\widetilde L | K` (`infiniteNormSubgroup`, M029.004, an infimum over the structure `FiniteIntermediateField (D.maximalUnramifiedField L) K`, M029.001, of the ranges `finiteIntermediateNormRange`, M029.003), where `D.maximalUnramifiedField L` (M029.016) is the maximal unramified extension `\widetilde L`. The target says that this intersection is contained in the norm subgroup from the particular finite field `L`. No hypothesis is added.

## Imports and dependencies

The module imports only the published statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.Statements`, unchanged. It defines the target and imports `finiteNormSubgroup` (M039.001), `maximalUnramifiedNormSubgroup` (M029.024), `infiniteNormSubgroup` (M029.004), `finiteIntermediateNormRange` (M029.003), the structure `FiniteIntermediateField` (M029.001) and `maximalUnramifiedField` (M029.016).

The source proof also uses the definition M039.018 `DegreeData.fieldAsMaximalUnramifiedIntermediate` (the field `L` regarded as a finite intermediate field of `\widetilde L | K`), which is in an accepted candidate but not yet in the Library at this module's base. The proof therefore writes that definition's body inline (see below) and does not import it.

The module opens `KummerTheory` and declares the variables, as the source does; the source's `open CyclicCohomology` is not needed.

## Implemented proof

The `show` that begins the proof states the published proposition with its left-hand side unfolded. The source proof first rewrites with M029.025 `maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup`, a `rfl` theorem whose proof is not yet in the Library; the port states the rewritten goal `infiniteNormSubgroup A (D.maximalUnramifiedField L) K ≤ finiteNormSubgroup A K L hLK` with `show` instead (the two sides agree by definition). Then, as in the source, `rw [infiniteNormSubgroup]` exposes the infimum `⨅ M : FiniteIntermediateField (D.maximalUnramifiedField L) K, finiteIntermediateNormRange A (D.maximalUnramifiedField L) K M`, and `iInf_le_of_le` at one finite intermediate field reduces the goal to the norm subgroup of that field. The source takes the field `D.fieldAsMaximalUnramifiedIntermediate K L hLK` (M039.018); the port takes the structure literal that is its body,

```lean
({ field := L
   above := show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
     inf_le_left
   below := hLK
   finite := hfinite } :
  FiniteIntermediateField (D.maximalUnramifiedField L) K)
```

with field `L`. The field `above` is the final step `inf_le_left` of the source proof of M029.019 `maximalUnramifiedField_le` (unpublished proof): `D.maximalUnramifiedField L` is by definition `D.fieldInertia L`, the closed subgroup `L ⊓ D.inertia`, so `inf_le_left` checks by definitional unfolding (the source first rewrites with the `rfl` theorem M029.017 `maximalUnramifiedField_eq_fieldInertia`). The instance `hfinite` supplies `finite`, since `extensionSubgroup K L hLK` is by definition `L.toSubgroup.subgroupOf K.toSubgroup`. This is the literal of the accepted M039.018 candidate; `above` is a proof, so the structure is the same by proof irrelevance. Finally `rfl` closes the goal: the norm range of this intermediate field is by definition `finiteNormSubgroup A K L hLK`. The development check reported only the axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passages are
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`, lines 227–231 and 298–304](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean#L227-L304) and [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`, lines 233–241 and 254–265](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean#L233-L265):
in `NormSubgroup.lean`, the theorem M029.019 with its docstring at lines 227–231, whose last step gives the field `above`, and the `rfl` theorem M029.025 with its docstring at lines 298–304, which the source proof rewrites with; in `FiniteNormQuotient.lean`, the definition M039.018 at lines 233–241 (in `section finiteIntermediateField`, line 227, with `variable {G : Type u} [Group G] [TopologicalSpace G]`, line 229), whose body the proof writes inline, and the target's docstring at lines 254–255 and theorem at lines 256–265. The `FiniteNormQuotient.lean` passages lie after `universe u` (line 18) in `namespace ClassFormation` (line 20), with `open KummerTheory` (line 22) and `open CyclicCohomology` (line 24), and its `noncomputable section` (line 28); the targets lie in `section quotientMaps` (line 247) with `variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 250) and `namespace DegreeData` (line 252). The source passages are:

```lean
/-- Every finite unramified field lies below the maximal unramified field. -/
theorem maximalUnramifiedField_le (D : DegreeData G) (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left
```

```lean
/-- `L` itself is a finite intermediate field of `\widetilde L | K`. -/
def fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := D.maximalUnramifiedField_le L
  below := hLK
  finite := hfinite
```

```lean
/-- The maximal-unramified norm subgroup is the infinite norm subgroup for
the maximal unramified field. -/
theorem maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.maximalUnramifiedNormSubgroup A K L =
      infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rfl
```

```lean
/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L`. -/
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
  rfl
```

The complete original files are retained at `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean` (SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`) and `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean` (SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`).

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement D A K L hLK` as its type, and begin the proof with `show` stating it with the left-hand side unfolded to `infiniteNormSubgroup A (D.maximalUnramifiedField L) K`, in place of the source's `rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]`;
- write the finiteness binder with the `Subgroup.subgroupOf` body of `extensionSubgroup`, as the published statement does;
- omit `open CyclicCohomology` and all other source declarations.

Modifications by Worker 743 on 16 November 2026:

- drop the import of the module of M039.018, which is not yet in the Library, and in the `iInf_le_of_le` step replace `D.fieldAsMaximalUnramifiedIntermediate K L hLK` by its body, the structure literal above, with `above` proved by `show … from inf_le_left` (the last step of the source proof of M029.019);
- extend the modification record in the Lean header and this Markdown accordingly.

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

This module proves only M039.019. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
