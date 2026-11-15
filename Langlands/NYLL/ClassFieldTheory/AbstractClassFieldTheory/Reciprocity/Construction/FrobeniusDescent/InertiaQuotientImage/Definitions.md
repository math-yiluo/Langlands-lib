# NYLL M017.001: the image of `G_L` in the inertia quotient `G_K / I_L`

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`.
The pinned source file has SHA-256
`75b2b32aeb8d07b1534b1ceb6c60052c71544a6029e1bc519c88905d9f63495f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.DegreeData.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- |
| M017.001 | `extensionImageInInertiaQuotient` | 31 | 32–38 | `extensionImageInInertiaQuotient` |

The source context is `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25), the
variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 27) and
`namespace DegreeData` (line 29). The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup`
and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField`
(lines 7–8). The other declarations of the source file are outside this
contribution.

The definition uses these published declarations:

- `DegreeData G` (M010.002, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the
  degree datum: a continuous homomorphism `degree : G →ₜ* ZHatMul`, where
  `ZHatMul` is `Multiplicative ZHat`, with `degree_surjective`;
- `D.extensionInertiaWithin K L hLK` (M012.002, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`), the subgroup
  `L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K` of
  `K.toSubgroup`, where `D.fieldInertiaWithin K` (M010.014) is the kernel of
  the restricted degree `D.restrictedDegree K` (M010.008) on `G_K`; that is
  the inertia subgroup `I_L` of `L`, viewed inside `G_K`;
- the instance `DegreeData.extensionInertiaWithin_normal` (M012.003, from
  the same module), which makes `D.extensionInertiaWithin K L hLK` normal
  whenever `(L.toSubgroup.subgroupOf K.toSubgroup).Normal`, so that the
  quotient `K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK` is a group;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup` and the subspace topology on `K.toSubgroup`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions` and
`Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`.

## Definition and complete telescope

The definition has, before the binders shown, the binders of the source
variable line 27: implicit `{G : Type*}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def extensionImageInInertiaQuotient (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Subgroup (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  (extensionSubgroup K L hLK).map
    (QuotientGroup.mk' (D.extensionInertiaWithin K L hLK))
```

For a degree datum `D`, closed subgroups `K` and `L` with `G_L ≤ G_K` and
`G_L` normal in `G_K`, this is the image of `G_L` under the quotient map
`G_K → G_K / I_L`, as a subgroup of the quotient group. The instance
hypothesis `hLnormal` is used through instance resolution: it is the
hypothesis of M012.003, which makes `I_L` normal in `G_K`, so that the
quotient is a group and `QuotientGroup.mk'` is a homomorphism.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition lies in
   `Langlands.NYLL.ClassFormation.DegreeData`.
2. Copy the docstring, the binders and the body verbatim.
3. Replace the source imports by the two focused published imports above
   and the source module docstring by a description of this module with a
   modification notice.
4. Keep the namespaces, `open CyclicCohomology`, the noncomputable section
   and the variable line 27; omit the rest of the source file.
5. No helper declaration, instance or linter option is added.

It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

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
