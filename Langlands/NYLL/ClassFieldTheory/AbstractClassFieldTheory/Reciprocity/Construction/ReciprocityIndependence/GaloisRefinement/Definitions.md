# NYLL M033.005 and M033.007: the Galois refinement of a finite intermediate field and its normality

The paired Lean file adapts the definition `ClassFormation.FiniteIntermediateField.galoisRefinement` and the instance `ClassFormation.FiniteIntermediateField.galoisRefinement_normal` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`.
The pinned source file has SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source declaration after `ClassFormation.FiniteIntermediateField.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M033.005 | `def galoisRefinement` | 82–83 | 84–111 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.galoisRefinement` |
| M033.007 | `instance galoisRefinement_normal` | 121 | 122–130 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.galoisRefinement_normal` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`section groupTheoreticRefinements` (line 29), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 31) and
`namespace FiniteIntermediateField` (line 33). The source imports are the
unported modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
(lines 7–8). The theorem M033.006 `galoisRefinement_le_field` (source lines
113–119), which lies between the two declarations, is stated in the sibling
module `Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Statements`.
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
- `KummerTheory.mem_extensionSubgroup_iff K L hLK k` (M022.001, the
  published theorem of
  `GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs`),
  whose type is the published target
  `mem_extensionSubgroup_iffStatement K L hLK k`, by definition
  `k ∈ L.toSubgroup.subgroupOf K.toSubgroup ↔ (k : G) ∈ L`: membership in
  `G_L` regarded as a subgroup of `G_K` is ambient membership in `G_L`;
- `FiniteIntermediateField.normalCoreField M` (M033.001, from the published
  module `Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions`),
  the closed subgroup of `G` obtained by mapping the normal core of
  `extensionSubgroup K M.field M.below` in `G_K` into `G` by
  `K.toSubgroup.subtype`.

`ClosedSubgroup`, `IsTopologicalGroup`, `Subgroup.Normal`,
`Subgroup.normalCore`, `Subgroup.normal_le_normalCore`,
`Subgroup.FiniteIndex`, `Subgroup.finiteIndex_of_finite_quotient` and
`Subtype.ext` are Mathlib's.

## Definition M033.005

The definition has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def galoisRefinement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    FiniteIntermediateField E K where
  field := M.normalCoreField
  above := by
    intro e he
    let eK : K.toSubgroup := ⟨e, M.below (M.above he)⟩
    have heE : eK ∈ extensionSubgroup K E (M.above.trans M.below) :=
      (mem_extensionSubgroup_iff K E (M.above.trans M.below) eK).2 he
    have hle : extensionSubgroup K E (M.above.trans M.below) ≤
        extensionSubgroup K M.field M.below := by
      intro x hx
      apply (mem_extensionSubgroup_iff K M.field M.below x).2
      exact M.above
        ((mem_extensionSubgroup_iff K E (M.above.trans M.below) x).1 hx)
    have heCore : eK ∈ (extensionSubgroup K M.field M.below).normalCore :=
      (Subgroup.normal_le_normalCore.mpr hle) heE
    exact ⟨eK, heCore, rfl⟩
  below := by
    rintro g ⟨k, _, rfl⟩
    exact k.2
  finite := by
    let H := extensionSubgroup K M.field M.below
    let : H.FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _ H M.finite
    let : H.normalCore.FiniteIndex := inferInstance
    have hcore : extensionSubgroup K M.normalCoreField
        (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
          rintro g ⟨k, _, rfl⟩
          exact k.2) =
        (extensionSubgroup K M.field M.below).normalCore := by
      ext k
      constructor
      · intro hk
        obtain ⟨k', hk', hk'n⟩ := hk
        have hk'eq : k' = k := by
          apply Subtype.ext
          exact hk'n
        simpa [hk'eq] using hk'
      · intro hk
        exact ⟨k, hk, rfl⟩
    rw [hcore]
    infer_instance
```

For a finite intermediate field `E | M | K` such that `G_E` is normal in
`G_K` (the source's hypothesis that the bottom extension `E | K` is
Galois), the Galois refinement is the finite intermediate field whose closed
subgroup is the normal core field `M.normalCoreField` (M033.001): the normal
core of `G_M` in `G_K`, which corresponds to the Galois closure of `M` over
`K`. Its three proof fields show that `G_E` lies in this normal core (since
`G_E` is normal in `G_K` and contained in `G_M`), that the normal core lies
in `G_K`, and that it has finite index in `G_K` (since `G_M` has finite
index).

The data field `field := M.normalCoreField` is the source's. The proof
field `above` is the source's verbatim: `mem_extensionSubgroup_iff`
resolves to the published M022.001 through `open KummerTheory`, and `.1`
and `.2` unfold its Statement type to the equivalence. The other two proof
fields differ from the source only as follows:

1. `below`: the source term `M.normalCoreField_le` is the proof of M033.002
   `normalCoreField_le`, whose statement is published (as
   `normalCoreField_leStatement` in
   `Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Statements`)
   but whose proof is not. It is replaced by that theorem's source proof
   (lines 55–56), `rintro g ⟨k, _, rfl⟩` then `exact k.2`.
2. `finite`: the source rewrites with `M.extensionSubgroup_normalCoreField`,
   the proof of M033.004, which is also not published. The adaptation
   proves the same equation as a local `have hcore` by the source proof of
   M033.004 (lines 71–80, verbatim), whose statement writes the inline proof
   of item 1 as the third argument of `extensionSubgroup` in place of
   `M.normalCoreField_le`, as the published target
   `extensionSubgroup_normalCoreFieldStatement` does. Then `rw [hcore]`
   replaces the source `rw [M.extensionSubgroup_normalCoreField]`. The
   other lines are the source's.

## Instance M033.007

The instance has the same leading binders, followed by:

```lean
instance galoisRefinement_normal [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (extensionSubgroup K (M.galoisRefinement).field
      (M.galoisRefinement).below).Normal := by
  have hcore : extensionSubgroup K M.normalCoreField
      (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
        rintro g ⟨k, _, rfl⟩
        exact k.2) =
      (extensionSubgroup K M.field M.below).normalCore := by
    ext k
    constructor
    · intro hk
      obtain ⟨k', hk', hk'n⟩ := hk
      have hk'eq : k' = k := by
        apply Subtype.ext
        exact hk'n
      simpa [hk'eq] using hk'
    · intro hk
      exact ⟨k, hk, rfl⟩
  change (extensionSubgroup K M.normalCoreField
    (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
      rintro g ⟨k, _, rfl⟩
      exact k.2)).Normal
  rw [hcore]
  infer_instance
```

The subgroup `G_core` representing the Galois refinement is normal in
`G_K`, because it is the normal core of `G_M` in `G_K`. The type of the
instance is the source's verbatim. In the proof, the local `have hcore` is
the same source proof of M033.004 as in the definition; the source
`change (extensionSubgroup K M.normalCoreField M.normalCoreField_le).Normal`
writes the inline source proof of M033.002 in place of
`M.normalCoreField_le`; and `rw [hcore]` replaces
`rw [M.extensionSubgroup_normalCoreField]`. The final `infer_instance` is
the source's.

Both declarations depend only on published declarations (including the
proved M022.001) and Mathlib; they contain no unproved assumption. Every replacement is a proof of a
proposition, so the data of `galoisRefinement` and the type of
`galoisRefinement_normal` are those of the source.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above. `open KummerTheory` resolves `mem_extensionSubgroup_iff`
   and `open CyclicCohomology` resolves `extensionSubgroup`.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions`
   (M033.001, which also brings M029.001 and M004.002) and
   `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs`
   (M022.001).
3. Replace the uses of the unpublished proofs of M033.002 and M033.004 in
   the proof fields as described above.
4. Replace the source module docstring by a description of this module with
   a modification notice that names the source declarations.
5. Omit the rest of the source file. Retain `universe u`, both opens, the
   noncomputable section, the section `groupTheoreticRefinements`, its
   variable line and the namespaces.
6. The binders, docstrings, data and the instance type are unchanged.

No helper declaration is added. This module discharges no host
class-formation, cup, transfer, Tate or reciprocity target.

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
