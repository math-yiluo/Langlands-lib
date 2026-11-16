# NYLL M027.003, M027.005, M027.006: targets that conjugation preserves residue degrees and normalized valuations

The paired Lean file adapts the statements of three theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`.
The pinned source file has SHA-256
`f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- |
| M027.003 | `DegreeData.FiniteResidueAbstractField.residueDegree_conjugate` | 66–67 | 68–71 | 71–82 | `DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement` |
| M027.005 | `FiniteAbstractField.residueDegree_conjugate` | 96 | 97–101 | 101–112 | `FiniteAbstractField.residueDegree_conjugateStatement` |
| M027.006 | `ValuationData.normalizedValuation_conjugate` | 116–118 | 119–124 | 124–202 | `ValuationData.normalizedValuation_conjugateStatement` |

M027.006 lies in `namespace ValuationData` (lines 114 and 204).

The source file imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws`
(lines 7–8). Its context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25), the comment and variable lines 27–29,

```lean
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}
```

and the closing lines 206–207.

The port keeps this context verbatim and in the same order. The first two
targets bind their own `{G : Type*} [Group G] [TopologicalSpace G]` (and
M027.003 also `{D : DegreeData G}`), exactly as the source theorems, so the
variable lines do not enter them; they have one universe parameter, that of
`G`. M027.006 uses the variable lines: its telescope begins with the
implicit `{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`; the group
lies in `Type 0`, and the carrier of `A` has an arbitrary universe, the
single universe parameter `u_1` reported by declaration inspection. Each
target is a `Prop`.

The names used resolve to published `Langlands.NYLL` declarations: the
conjugate `DegreeData.FiniteResidueAbstractField.conjugate` (M027.002,
ported in the companion module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Definitions`
of this contribution); `DegreeData.FiniteResidueAbstractField` (M010.021) and
its positive residue degree `DegreeData.FiniteResidueAbstractField.residueDegree`
(M010.025), both in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`;
`FiniteAbstractField` (M010.121, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`) and its residue
degree `FiniteAbstractField.residueDegree K D` (M010.127, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`); the
conjugate finite field `FiniteAbstractField.conjugate` (M027.004, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FiniteAbstractFieldConjugate.Definitions`); the
conjugate element `conjugateFixedElement A K σ a`, the element
`A.ρ σ⁻¹ a` of `ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)`
(M026.003, in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`);
`ValuationData` (M025.012) and the normalized valuation
`ValuationData.valuationAt` (M025.025, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`), all in
`ClassFormation`; `DegreeData` (M010.002);
`KummerTheory.ambientFixedAddSubgroup` (M023.001, found through
`open KummerTheory`); and `IntegralRepGroupType` (M002.001). Mathlib
supplies `ContinuousMul`, `Rep`, `ℕ+` and the coercions.

## Targets and complete telescopes

### M027.003

```lean
/-- The proposition, from the source theorem
`DegreeData.FiniteResidueAbstractField.residueDegree_conjugate`, that
conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
def DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    Prop :=
    (K.conjugate σ).residueDegree = K.residueDegree
```

Conjugating a residue-finite abstract field by `σ` preserves its positive
absolute residue degree.

### M027.005

```lean
/-- The proposition, from the source theorem
`FiniteAbstractField.residueDegree_conjugate`, that conjugation preserves the
positive absolute residue degree. -/
def FiniteAbstractField.residueDegree_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G)
    (D : DegreeData G) (σ : G) : Prop :=
    (K.conjugate σ).residueDegree D = K.residueDegree D
```

Conjugating a finite abstract field by `σ` preserves its residue degree with
respect to the degree data `D`.

### M027.006

```lean
/-- The proposition, from the source theorem `normalizedValuation_conjugate`
(conjugation compatibility of normalized valuations), that the normalized
valuations are compatible with conjugation: `v_{K^σ}(a^σ) = v_K(a)` (the
right-action notation). -/
def normalizedValuation_conjugateStatement [ContinuousMul G]
    (v : ValuationData D A) (K : FiniteAbstractField G) (σ : G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    v.valuationAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) =
      v.valuationAt K a
```

For a valuation datum `v`, a finite abstract field `K`, `σ ∈ G` and `a` in
`A_K = ambientFixedAddSubgroup A K.field`, the normalized valuation of the
conjugate field `K^σ` at the conjugate element `a^σ` equals the normalized
valuation of `K` at `a`, that is, `v_{K^σ}(a^σ) = v_K(a)`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line (for M027.003,
   `Prop :=` stands on its own line after the telescope). The source proofs
   are omitted: this contribution publishes the proposition targets, and
   their proofs are separate work.
3. Replace each source docstring by a description of the proposition that
   names the source theorem, and the source module docstring by a
   description of this module with a modification notice.
4. Replace the two source imports by the companion module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Definitions` and the published
   modules `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FiniteAbstractFieldConjugate.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions` and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`, which
   import the modules of all names listed above.
5. Keep the source context listed above; omit M027.001, M027.002 (ported in
   the companion module), M027.004 (published) and the other declarations
   of the source file. No helper declaration, instance or linter option is
   added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings. Declaration inspection of M027.006 reported a `Prop` target, one universe parameter and the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
