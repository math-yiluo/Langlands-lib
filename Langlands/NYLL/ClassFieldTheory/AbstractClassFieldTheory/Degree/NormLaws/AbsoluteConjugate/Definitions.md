# NYLL M026.007: conjugation of absolute coset spaces

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`.
The pinned source file has SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- |
| M026.007 | `absoluteConjugateCosetEquiv` | 112 | 113–130 | `absoluteConjugateCosetEquiv` |

The source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), `open scoped BigOperators Pointwise`
(line 26) and the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29, after
the comment line 28). The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.GaloisCohomology.GroupTheory.QuotientTower` (lines 7–8). The other
declarations of the source file are outside this contribution.

The definition uses these published declarations:

- `baseField G` (M010.003, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the closed
  subgroup `⊤` of `G`, the distinguished base field, and `le_baseField K`
  (M010.005, proved in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`), whose type
  `le_baseFieldStatement K` is `K.toSubgroup ≤ (baseField G).toSubgroup`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- `conjugateClosedSubgroup_mem` (M026.002, proved in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`), whose type is
  `conjugateClosedSubgroup_memStatement K σ x` (from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`), the proposition
  `x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K`;
- `Langlands.NYLL.PortInternal.M026.d005 σ` (M026.005, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the published name of the private
  source definition `absoluteConjugationEquiv`: the equivalence of
  `(baseField G).toSubgroup` with itself sending `x` to `σ * x.1 * σ⁻¹`, with
  inverse `x ↦ σ⁻¹ * x.1 * σ`;
- `Langlands.NYLL.PortInternal.M026.d006` (M026.006, proved in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U006.Proofs`), the published name of the private
  source theorem `mem_absoluteExtension`, whose type
  `Langlands.NYLL.PortInternal.M026.d006Statement K x` is
  `x ∈ extensionSubgroup (baseField G) K (le_baseField K) ↔ x.1 ∈ K`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup`, and Mathlib's `Rep ℤ G`, with the underlying group `A.V`
  and the action `A.ρ`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs` and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U006.Proofs`, which import the other declarations
above.

## Definition and complete telescope

The definition binds its own `{G : Type*}`, which shadows the variable of
line 29, so its telescope is complete as shown.

```lean
noncomputable def absoluteConjugateCosetEquiv
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) :
    ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) ≃
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K)) :=
  Quotient.congr (Langlands.NYLL.PortInternal.M026.d005 σ) (by
    intro x y
    have hext : ∀ (H : ClosedSubgroup G) (z : (baseField G).toSubgroup),
        z ∈ extensionSubgroup (baseField G) H (le_baseField H) ↔ z.1 ∈ H :=
      fun H z => Langlands.NYLL.PortInternal.M026.d006 H z
    have hmem : ∀ z : G, z ∈ conjugateClosedSubgroup K σ ↔ σ * z * σ⁻¹ ∈ K :=
      fun z => conjugateClosedSubgroup_mem K σ z
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
      hext, hext,
      hmem]
    change σ * (x.1⁻¹ * y.1) * σ⁻¹ ∈ K.toSubgroup ↔
      (σ * x.1 * σ⁻¹)⁻¹ * (σ * y.1 * σ⁻¹) ∈ K.toSubgroup
    simp [mul_assoc])
```

For a closed subgroup `K` of a topological group `G` with continuous
multiplication and `σ : G`, this is the equivalence of the absolute coset
spaces `G ⧸ G_{K^σ}` and `G ⧸ G_K` (both taken inside
`(baseField G).toSubgroup`) given on cosets by `x ↦ σ * x * σ⁻¹`. It is
`Quotient.congr` of the equivalence `PortInternal.M026.d005 σ` with a proof
that it respects the two left coset relations.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.absoluteConjugateCosetEquiv`.
2. Refer to the private source definition `absoluteConjugationEquiv`
   (M026.005) by its published name `Langlands.NYLL.PortInternal.M026.d005`.
3. In the proof that the coset relations correspond, the source rewrites
   `rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
   mem_absoluteExtension, mem_absoluteExtension,
   conjugateClosedSubgroup_mem]`. The published theorems
   `PortInternal.M026.d006` (the private source `mem_absoluteExtension`) and
   `conjugateClosedSubgroup_mem` have the Prop-valued types
   `d006Statement H z` and `conjugateClosedSubgroup_memStatement K σ z`,
   which `rw` does not unfold. The proof therefore first states the two
   equivalences as local hypotheses `hext` and `hmem`, proved by those
   theorems, and rewrites with `hext, hext, hmem` in the same order. The
   following `change` and `simp [mul_assoc]` are unchanged. The change is
   inside the proof of a proposition (the second argument of
   `Quotient.congr`), so the equivalence and its maps are those of the
   source.
4. Copy the docstring, the binders and the rest of the body verbatim.
5. Replace the source imports by the two focused published imports above
   and the source module docstring by a description of this module with a
   modification notice.
6. Keep the namespace, both opens, the noncomputable section,
   `open scoped BigOperators Pointwise`, the comment line 28 and the variable
   line 29; omit the rest of the source file.
7. No helper declaration, instance or linter option is added.

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
