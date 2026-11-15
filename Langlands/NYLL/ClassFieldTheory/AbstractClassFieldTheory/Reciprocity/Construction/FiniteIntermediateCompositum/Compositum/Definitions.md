# NYLL M034.001: the compositum of two finite intermediate fields

The paired Lean file adapts the definition `ClassFormation.FiniteIntermediateField.compositum` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`.
The pinned source file has SHA-256
`579d38da784d715ecd9a49a310408856e4235252d3b5940440f7b17684c303b1`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.FiniteIntermediateField.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M034.001 | `compositum` | 29 | 30–40 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositum` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open CyclicCohomology` (line 19), `noncomputable section` (line 23), the
variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 25) and
`namespace FiniteIntermediateField` (line 27). The source import is the
unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence`
(line 7). The targets M034.002/.003 `compositum_le_left`/`_le_right` are in
the sibling module
`Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Statements`.
The rest of the source file is not part of this module.

The names used resolve as follows:

- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a structure with a
  closed subgroup `M.field`, `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and the finiteness
  `M.finite` of `K.toSubgroup ⧸ extensionSubgroup K M.field M.below`: an
  intermediate field `E | M | K` finite over `K`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a
  subgroup of `G_K`;
- `FiniteIntermediateField.compositumWith M S` (M033.008, from the published
  module `Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions`),
  the closed subgroup `M.field ⊓ S`, that is `G_M ∩ G_Σ`, representing the
  field compositum `MΣ`.

`ClosedSubgroup`, `Finite`, `inf_le_left`, `inf_le_right`,
`Subgroup.relIndex`, `Subgroup.index_ne_zero_of_finite`,
`Nat.finite_of_card_ne_zero`, `Subgroup.mem_subgroupOf`,
`Subgroup.mem_inf` and `Subgroup.relIndex_inf_ne_zero` are Mathlib's.

## Definition

The definition has the binders implicit `{G : Type*}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def compositum {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    let : Finite
        (K.toSubgroup ⧸ extensionSubgroup K N.field N.below) := N.finite
    have hMindex : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
      rw [Subgroup.relIndex]
      exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
        (extensionSubgroup K M.field M.below) M.finite
    have hSindex : N.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
      rw [Subgroup.relIndex]
      exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
        (extensionSubgroup K N.field N.below) N.finite
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup K (M.compositumWith N.field)
        ((show (M.compositumWith N.field).toSubgroup ≤ N.field.toSubgroup from
          inf_le_right).trans N.below)).index ≠ 0
    have hsub : extensionSubgroup K (M.compositumWith N.field)
        ((show (M.compositumWith N.field).toSubgroup ≤ N.field.toSubgroup from
          inf_le_right).trans N.below) =
        (M.field.toSubgroup ⊓ N.field.toSubgroup).subgroupOf K.toSubgroup := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      rfl
    rw [hsub]
    simpa only [Subgroup.relIndex] using
      Subgroup.relIndex_inf_ne_zero hMindex hSindex
```

For finite intermediate fields `M` and `N` of `E | K`, their compositum
`MN` is represented by the closed subgroup `G_M ∩ G_N`. It contains `G_E`,
lies in `G_K` and has finite index in `G_K`. The data field
`field := M.field ⊓ N.field` and the proof fields `above` and `below` are
the source's verbatim.

In the proof field `finite`, the `let` line is the source's. The source
then concludes with `exact M.compositumWith_finite_over_base N.field N.below`,
an application of the theorem M033.014, whose statement is stated in
`Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Finiteness.Statements`
but whose proof is not published. The adaptation replaces this line by the
source proof of M033.014 (`ReciprocityIndependence.lean` lines 226–245)
specialized to `S := N.field`, `hSK := N.below` and
`hSfinite := N.finite`, the value of the preceding `let`:

1. `M.compositumWith_le_right S` (M033.010, proof not published) is written
   as its source proof
   `show (M.compositumWith N.field).toSubgroup ≤ N.field.toSubgroup from inf_le_right`;
2. `rw [mem_extensionSubgroup_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]`
   becomes `rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]`.
   The source rewrites with `mem_extensionSubgroup_iff` (M022.001,
   `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean` lines
   33–38, proved by `Iff.rfl`). Its published form
   `Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iff` (module
   `GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs`)
   has the type `mem_extensionSubgroup_iffStatement K L hLK k`, a Prop-valued
   definition, so `rw` cannot use it as an equivalence directly. Because
   `extensionSubgroup` is the abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`,
   the first rewrite uses Mathlib's `Subgroup.mem_subgroupOf` instead, which
   states the same equivalence for the unfolded subgroup and is also proved by
   `Iff.rfl`; the second rewrite is the source's.

The `change` step shows that the goal produced by
`Nat.finite_of_card_ne_zero` is the index of
`extensionSubgroup K (M.compositumWith N.field) _`, which is the subgroup of
the quotient in the field `finite`, because `M.compositumWith N.field`
unfolds to `M.field ⊓ N.field`. The definition depends only on published
declarations and Mathlib and contains no unproved assumption.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above. `open CyclicCohomology` resolves `extensionSubgroup`.
2. Replace the source import by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions`
   (M033.008, which also brings M029.001 and M004.002).
3. In the proof field `finite`, replace the application of the unpublished
   theorem M033.014 by its specialized source proof, as described above.
4. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
5. Omit the rest of the source file. Retain `open CyclicCohomology`, the
   noncomputable section, the variable line and the namespaces.
6. The binders, docstring and data are unchanged.

No helper declaration or instance is added. This definition discharges no
host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
