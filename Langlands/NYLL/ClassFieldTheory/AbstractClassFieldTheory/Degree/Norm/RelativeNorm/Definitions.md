# NYLL M024: the relative norm homomorphism

The paired Lean file adapts one data definition from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`,
SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

| Unit | Source name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M024.009 | `ClassFormation.relativeNorm` | 138–161 (docstring 138–142, declaration 143–161) | `Langlands.NYLL.ClassFormation.relativeNorm` |

The enclosing source context is `namespace ClassFormation` (line 22),
`open KummerTheory` (line 24), `open CyclicCohomology` (line 25),
`noncomputable section` (line 29), `open scoped BigOperators` (line 31) and
the group variables at line 34. The source docstring (lines 138–142) is
retained verbatim.

## Object and complete telescope

`relativeNorm` has the source's implicit `{G : IntegralRepGroupType}`,
followed by `[Group G]` and `[TopologicalSpace G]`. The published
`Langlands.NYLL.IntegralRepGroupType` is exactly `Type 0`. The representation
`A : Rep ℤ G` has an arbitrary carrier universe, so the declaration has one
universe parameter for that carrier; the acting group remains in universe zero.

It then takes, explicitly and in order, `A : Rep ℤ G`,
`K L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.toSubgroup`, followed by
the instance argument
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`.
Its result is the additive monoid homomorphism

```lean
ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K
```

between the actual fixed submodules `A_L` and `A_K` of the representation
module, both given by the published
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001). There is
no Galois (normality) hypothesis, no topological-group hypothesis and no
continuity assumption on the representation.

The construction is the source structure instance:

- `toFun a` is the subtype element
  `⟨relativeNormValue A K L hLK a, relativeNormValue_fixed A K L hLK a⟩`.
  Its value is the published coset sum `relativeNormValue` (M024.005,
  the sum of `relativeCosetAction A K L hLK a q` over all cosets
  `q` of the actual finite relative quotient), and its membership proof is
  the published proof `Langlands.NYLL.ClassFormation.relativeNormValue_fixed`
  of M024.008, whose type is the published Prop
  `relativeNormValue_fixedStatement`; that Prop unfolds definitionally to the
  `K`-fixedness condition defining `ambientFixedAddSubgroup A K`.
- `map_zero'` is proved by `Subtype.ext`, installing `Fintype.ofFinite` for
  the relative quotient and a `simp` call over `relativeNormValue`; see the
  single modification below.
- `map_add'` is the source proof unchanged: `Subtype.ext`,
  `Fintype.ofFinite`, `simp only [AddSubgroup.coe_add, relativeNormValue]`,
  `← Finset.sum_add_distrib`, `Finset.sum_congr rfl`, and termwise the
  published proof `Langlands.NYLL.ClassFormation.relativeCosetAction_add` of
  M024.006.

## Reuse of the relative subgroup

Source M004.002, `CyclicCohomology.extensionSubgroup`, is defined at
lines 47–54 of `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` at the
same pin (SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`), with
complete telescope
`{G : Type u} [Group G] [TopologicalSpace G] (K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup)`
and abbreviation body `L.toSubgroup.subgroupOf K.toSubgroup`. As in the
published M024 data and statement modules
(`Degree/Norm/Definitions.lean`, `Degree/Norm/Statements.lean`) and the
published M010 extension objects, each occurrence of
`extensionSubgroup K L hLK` is replaced by this exact body, Mathlib's
`Subgroup.subgroupOf`. The inclusion hypothesis `hLK` stays in the
telescope. This keeps the finite instance syntactically identical to the one
taken by the published `relativeNormValue` and supplied by the published
`DegreeData.FiniteAbstractExtension.representedQuotientFinite`.

## Modifications

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix `ClassFormation` by `Langlands.NYLL`; `KummerTheory` and
   `IntegralRepGroupType` resolve to the published namespaced support.
   Drop the unused `open CyclicCohomology`.
2. Replace the two original NYLL imports by the focused published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U006.Proofs`
   (proof of M024.006) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U008.Proofs`
   (proof of M024.008), which import the published M024 data.
3. Expand `extensionSubgroup` as described above, with parentheses around the
   replacement.
4. In the embedded `map_zero'` proof, the source's `simp [relativeNormValue]`
   (line 153) closes the goal `∑ q, relativeCosetAction A K L hLK 0 q = 0`
   only with the source simp lemma `relativeCosetAction_zero` (M024.007,
   lines 101–111), which is not published. The adapted proof therefore first
   proves the same fact as a local hypothesis `hzero`, by the source proof of
   M024.007 (quotient induction and `map_zero (A.ρ k.1)`) with its
   `simp only [relativeCosetAction_mk]` step replaced by an explicit
   definitional `change`, and then runs `simp [relativeNormValue, hzero]`.
   This changes only a proof of a `Prop` field; the homomorphism is the same.
5. Extract only this declaration and replace the module introduction with the
   extraction and modification notice.

No instance or other public declaration is introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; focused inspection of
`relativeNorm` reports axioms `propext`, `Classical.choice` and `Quot.sound`
only and one universe parameter.

A private probe reconstructs the source declaration verbatim (with the
source `extensionSubgroup` abbreviation in the finite instance, the source
`simp [relativeNormValue]` proof and a local reconstruction of the source
simp lemma `relativeCosetAction_zero`) and verifies
`@relativeNormSrc.{u} = @relativeNorm.{u}` by `rfl` for an arbitrary carrier
universe. This compares the entire dependent functions, telescopes included.
The probe is development evidence and supplies no public declaration.

This support data is internal to the NYLL abstract-field model. Its
evaluation equation is the separate statement target in
[`Statements.md`](Statements.md); the host class-formation, cup, transfer,
Tate and reciprocity obligations remain with their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 96's modifications are recorded in the Lean header and above.
