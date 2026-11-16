# The image of the extension subgroup in the inertia quotient is closed

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionImageInInertiaQuotient_isClosed`, the proof phase of
M017.002 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m017).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionImageInInertiaQuotient_isClosedStatement` applied to the
theorem's parameters:

```lean
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    extensionImageInInertiaQuotient_isClosedStatement D K L hLK
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type*} [Group G] [TopologicalSpace G]`. The theorem takes `D`, the instances `[IsTopologicalGroup G] [CompactSpace G] [T2Space G]`, `K`, `L`, `hLK` and the instance hypotheses `hLnormal` and `hLfinite`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.InertiaQuotientImage.Statements`, the target is the proposition

```lean
IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
  (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))
```

Here `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree : G →ₜ* ZHatMul` onto `ZHatMul = Multiplicative ZHat` (M010.001, M008.008), `K : FiniteResidueAbstractField D` (M010.021) is an abstract field with closed subgroup `K.field = G_K` and finite residue quotient, `L : ClosedSubgroup G` is a closed subgroup with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, `extensionSubgroup K.field L hLK` (M004.002, Mathlib's `L.toSubgroup.subgroupOf K.field.toSubgroup`) is `G_L` viewed inside `G_K`, assumed normal (`hLnormal`) and of finite index (`hLfinite`: the quotient is `Finite`), and `D.extensionInertiaWithin K.field L hLK` (M012.002) is the subgroup `L.toSubgroup.subgroupOf K.field.toSubgroup ⊓ D.fieldInertiaWithin K.field` of `G_K`, where `D.fieldInertiaWithin K.field` (M010.014) is the kernel of the restricted degree `D.restrictedDegree K.field : G_K →ₜ* ZHatMul` (M010.008); that is the inertia subgroup `I_L` of `L` viewed inside `G_K`; the published instance M012.003 makes it normal, so the quotient `G_K / I_L` is a topological group with the quotient topology. `D.extensionImageInInertiaQuotient K.field L hLK` (M017.001) is the image of `G_L` in `G_K / I_L`. The target says that this image is closed; `G` is a compact Hausdorff topological group. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.InertiaQuotientImage.Statements`, which defines the target and imports `extensionImageInInertiaQuotient` (M017.001), `extensionInertiaWithin` with its normality instance (M012.002, M012.003), `extensionSubgroup` (M004.002) and `FiniteResidueAbstractField` (M010.021);
- `Mathlib.Topology.Algebra.OpenSubgroup`, for Mathlib's `Subgroup.isClosed_of_isOpen` (an open subgroup is closed), which the source reaches through its NYLL imports.

The module does not import the proof of M014.022 (`DegreeData.extensionInertiaWithin_isClosed`, the closedness of `I_L` in `G_K`), which the source's first proof step cites; that step is unused and omitted (see below).

The module opens `CyclicCohomology`, as the source does, for `extensionSubgroup`.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof without its first step. That step, `let : IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) := D.extensionInertiaWithin_isClosed K L hLK`, adds the closedness of `I_L` as a local hypothesis; `IsClosed` is not a type class, so it is not an instance, and no later step uses it (none of the Mathlib lemmas below requires the quotient `G_K / I_L` to be Hausdorff: `QuotientGroup.isOpenMap_coe` and `Subgroup.isClosed_of_isOpen` need only `SeparatelyContinuousMul`). The proof compiles without it. With `E := extensionSubgroup K.field L hLK`, `hEclosed` shows that `E` is closed (its carrier is by `rfl` the preimage of `L` under the inclusion `G_K → G`), the finiteness of `G_K ⧸ E` gives `E.FiniteIndex` (`Subgroup.finiteIndex_of_finite_quotient`), and Mathlib's `Subgroup.isOpen_of_isClosed_of_finiteIndex` makes `E` open. After `change` writes the image as the image of `E` under `QuotientGroup.mk'`, the image is open by `QuotientGroup.isOpenMap_coe`, and an open subgroup is closed (`Subgroup.isClosed_of_isOpen`).

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`, lines 40–71](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean#L40-L71):
the docstring at lines 40–41 and the theorem at lines 42–71. It lies in `namespace ClassFormation` (line 19), with `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), the variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 27) and `namespace DegreeData` (line 29). The source is:

```lean
/-- The image of `G_L` in `G_K / I_L` is closed.  This is the compact-image
step implicit in the Galois correspondence used. -/
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let E := extensionSubgroup K.field L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`;
its SHA-256 is `75b2b32aeb8d07b1534b1ceb6c60052c71544a6029e1bc519c88905d9f63495f`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above; add the Mathlib import `Mathlib.Topology.Algebra.OpenSubgroup`, which the source reaches through its NYLL imports;
- give the theorem the published proposition `extensionImageInInertiaQuotient_isClosedStatement D K L hLK` as its type, and begin the proof with `show` stating it unfolded;
- omit all other source declarations.

Modifications by Worker 738 on 16 November 2026:

- omit the source's unused first proof step (lines 51–53, the `let : IsClosed …` citing `D.extensionInertiaWithin_isClosed`) and with it the import of the M014.022 proof module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.ExtensionInertiaClosed.U022.Proofs`.

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

This module proves only M017.002. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
