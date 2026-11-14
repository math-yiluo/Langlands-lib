# NYLL M026: conjugate closed subgroups, normal-extension action and finite-tower data

This file adapts five data declarations from Naganori Yamaguchi's
ClassFieldTheory, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`.
The source file SHA-256 is
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

Source names begin with `ClassFormation.`. Adapted names begin with
`Langlands.NYLL.ClassFormation.`, except the private source definition,
whose adapted name is given in full.

| Unit | Source name | Source lines (docstring; declaration) | Adapted name |
| --- | --- | --- | --- |
| M026.001 | `conjugateClosedSubgroup` | 31–33; 34–45 | `conjugateClosedSubgroup` |
| M026.005 | `absoluteConjugationEquiv` (private) | none; 92–103 | `Langlands.NYLL.PortInternal.M026.d005` |
| M026.011 | `normalExtensionAction` | 247–249; 250–268 | `normalExtensionAction` |
| M026.015 | `DegreeData.FiniteTower.totalExtension` | 334; 335–338 | `DegreeData.FiniteTower.totalExtension` |
| M026.016 | `DegreeData.FiniteTower.totalQuotientFinite` (instance) | 340; 341–345 | `DegreeData.FiniteTower.totalQuotientFinite` (instance) |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), `open scoped BigOperators Pointwise`
(line 26), the comment at line 28 and the section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29).
M026.015 and M026.016 lie in `namespace DegreeData.FiniteTower` (lines
330–347) with the section variable `(T : DegreeData.FiniteTower G)` at line
332. All of this context is reproduced in the paired Lean file.
The source docstrings of M026.001, .011, .015 and .016 are retained verbatim.

M026.015 is not in the task's listed units. It is ported because the listed
instance M026.016 uses it through the dot notation `T.totalExtension`, as the
task directs for unlisted same-module dependencies.

## Objects and complete telescopes

### M026.001 `conjugateClosedSubgroup`

The telescope is `{G : Type*} [Group G] [TopologicalSpace G]
[ContinuousMul G] (K : ClosedSubgroup G) (σ : G)`, and the result is a
`ClosedSubgroup G` (Mathlib's closed subgroups). As in the source, the
binder `{G : Type*}` shadows the section group, so the declaration has one
free universe parameter and does not use the section instances.

The subgroup field is the pointwise conjugate
`ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, which is `σ⁻¹ K σ`; the source
docstring calls this the subgroup of the conjugate field `K^σ`. The
closedness proof is unchanged: it identifies the subgroup with the preimage
of `K` under the continuous map `x ↦ σ * x * σ⁻¹`
(`IsTopologicalGroup.continuous_conj`), using
`Subgroup.mem_pointwise_smul_iff_inv_smul_mem` and the `ConjAct` simp lemmas.

### M026.005 `Langlands.NYLL.PortInternal.M026.d005`

The telescope is `{G : Type*} [Group G] [TopologicalSpace G] (σ : G)`,
again with a free universe. The result is a permutation
`(baseField G).toSubgroup ≃ (baseField G).toSubgroup` of the absolute
subgroup. `baseField G` is the published
`Langlands.NYLL.ClassFormation.baseField` (M010.003), the closed subgroup
whose subgroup is `⊤`. The forward map is `x ↦ ⟨σ * x.1 * σ⁻¹, trivial⟩`,
the inverse is `x ↦ ⟨σ⁻¹ * x.1 * σ, trivial⟩`, and the two inverse laws
are the source proofs `Subtype.ext` and `simp [mul_assoc]`. The source has no
docstring; the adapted declaration has one naming the source definition.

### M026.011 `normalExtensionAction`

The telescope is the section group `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]`, then explicit `A : Rep ℤ G`,
`K L : ClosedSubgroup G`, `hLK : L.toSubgroup ≤ K.toSubgroup`,
`hnormal : (extensionSubgroup K L hLK).Normal`, `k : K.toSubgroup` and
`a : ambientFixedAddSubgroup A L`, in that order. The result is
`ambientFixedAddSubgroup A L`. The published
`Langlands.NYLL.IntegralRepGroupType` is `Type 0`; the representation
carrier has a free universe, which is the declaration's one universe
parameter.

The value is `⟨A.ρ k.1 a.1, _⟩`, the action of `k` on the fixed element
`a`. The embedded proof that this value is fixed by every `l ∈ L` is the
source proof: it uses normality to show that `k⁻¹ * l * k` lies in the
relative subgroup, and rewrites `l * k = k * (k⁻¹ * l * k)` through
`map_mul` and the fixedness of `a`. Normality enters only this proof.

`extensionSubgroup` is the published abbreviation
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (source M004.002), whose
body is `L.toSubgroup.subgroupOf K.toSubgroup`. It is used by name, so the
source expression is unchanged. `ambientFixedAddSubgroup` is the published
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001), the
additive subgroup of `A.V` of elements fixed by every element of
`L.toSubgroup`.

### M026.015 `DegreeData.FiniteTower.totalExtension`

The telescope is the section group `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` and then the section variable
`(T : DegreeData.FiniteTower G)`, so the group is in `Type 0` and the
declaration has no universe parameter. `DegreeData.FiniteTower` is the
published M010.105, a tower `top ≤ middle ≤ base` of closed subgroups with
finite successive quotients, which supplies the instances
`topQuotientFinite` and `baseQuotientFinite`. The result is a published
`DegreeData.FiniteAbstractExtension G` (M010.065).

Its field `toAbstractExtension` is `T.toTower.totalExtension`, the published
composite extension with field `T.top` and base `T.base`, as in the source.
Its field `finiteQuotient` is the one modified part, described below.

### M026.016 `DegreeData.FiniteTower.totalQuotientFinite`

This instance has the same telescope as M026.015. It provides
`Finite (T.base.toSubgroup ⧸ extensionSubgroup T.base T.top
(T.top_le_middle.trans T.middle_le_base))`, with value
`T.totalExtension.finiteQuotient`, exactly as in the source. Like the
source, it is a global instance in namespace
`Langlands.NYLL.ClassFormation.DegreeData.FiniteTower`. Its class `Finite`
is a proposition, so it creates no data diamond. The Library has no other
instance for this total quotient; the existing
`topQuotientFinite` and `baseQuotientFinite` give the two successive
quotients.

## Modifications and verification

Worker 165 made only the following adaptations on 14 November 2026:

1. Prefix the namespace `ClassFormation` by `Langlands.NYLL`. The unqualified
   `KummerTheory`, `CyclicCohomology`, `IntegralRepGroupType`, `baseField`
   and `DegreeData` then resolve to the published names in that namespace.
2. Replace the two source imports (`Nyll...Degree.Valuation` and
   `Nyll.GaloisCohomology.GroupTheory.QuotientTower`) by focused imports:
   the Mathlib modules for pointwise subgroups, `ConjAct` and closed
   subgroups, and the published NYLL modules for `extensionSubgroup`,
   `ambientFixedAddSubgroup`, `Subgroup.quotientTowerEquiv`, `baseField`,
   `FiniteAbstractExtension` and `FiniteTower`.
3. Name the private source definition
   `Langlands.NYLL.PortInternal.M026.d005`, declared from inside the
   namespace with a `_root_` prefix, and add a docstring for it.
4. In M026.015, the source field is
   `finiteQuotient := relativeTowerQuotientFinite T.base T.middle T.top
   T.top_le_middle T.middle_le_base`, which applies the theorem M026.014. That
   theorem's proof is a separate proof task, so the adapted field is the
   source proof term of M026.014 (source lines 325–328) at these arguments:

   ```lean
   Finite.of_equiv
     ((T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base) ×
       (T.middle.toSubgroup ⧸ extensionSubgroup T.middle T.top T.top_le_middle))
     (Subgroup.quotientTowerEquiv T.top_le_middle T.middle_le_base).symm
   ```

   The two finiteness instances that the source theorem takes are found by
   instance search, as in the source application. The proof term is a
   proposition, so the structure value is unchanged up to proof
   irrelevance.
5. Extract only these five declarations. The theorems between them go to the
   paired statement module or to other tasks, and the remaining source data
   (for example M026.003 and M026.007) is not part of this task. Replace the
   module introduction with the extraction and modification notice.

The source `noncomputable section`, scopes, binder kinds and order,
declaration bodies and all other embedded proofs are unchanged. The only
instance is the source instance M026.016.

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Declaration inspection reports
one universe parameter for `conjugateClosedSubgroup`, `M026.d005` and
`normalExtensionAction`, and none for `totalExtension` and
`totalQuotientFinite`. Their axioms are among `propext`, `Classical.choice`
and `Quot.sound`.

A private focused probe checks by `rfl` that `T.totalExtension` equals the
source-shaped structure whose `finiteQuotient` applies a local copy of the
source theorem M026.014 with its source proof. It also checks that the
instance `totalQuotientFinite` is found by instance search for the source
quotient, and that the two functions of `M026.d005` are the source
conjugations. The probe supplies no public declaration.

This data belongs to the NYLL abstract-field model. The associated theorem
statements are in `NormLaws/Statements.lean`, and their proofs are separate
work, as are the host class-formation, cup, transfer, Tate and reciprocity
obligations.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 165's modifications are recorded in the Lean header and above.
