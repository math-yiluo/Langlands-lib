# Conjugation preserves the residue degree of a residue-finite field

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegree_conjugate`, the proof phase of
M027.003 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m027).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement` applied to the
theorem's parameters:

```lean
theorem DegreeData.FiniteResidueAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement
      K σ
```

## Target and binders

The theorem binds `{G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G} [ContinuousMul G]`, `K` and `σ`, exactly as the published target and the source theorem; it does not use the source file's variables.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Statements`, the target is the proposition

```lean
(K.conjugate σ).residueDegree = K.residueDegree
```

Here `G` is a topological group with continuous multiplication, `D : DegreeData G` (M010.002) a degree datum (a continuous homomorphism `D.degree` from `G` to the profinite integers written multiplicatively, `ZHatMul`), and `K : DegreeData.FiniteResidueAbstractField D` (M010.021) an abstract field: a closed subgroup `K.field` of `G` whose residue quotient `D.residueQuotient K.field` (M010.018, the quotient of `ZHatMul` by the degree image `D.fieldImage K.field`, M010.010) is finite. `K.conjugate σ` (M027.002) is the residue-finite field with field `conjugateClosedSubgroup K.field σ` (M026.001, the conjugate abstract field `K^σ`, with subgroup `σ⁻¹ K σ`), and `residueDegree` (M010.025) is the cardinality of the residue quotient as a positive natural number. The target says that conjugation does not change the residue degree. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Statements`, which defines the target and imports the conjugates M027.002 and M027.004, `conjugateClosedSubgroup` (M026.001), `DegreeData.fieldImage` (M010.010), `DegreeData.residueQuotient` (M010.018) and the residue degrees;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.U001.Proofs`, the published proof of M027.001 `DegreeData.fieldImage_conjugate`, whose type is the published proposition `DegreeData.fieldImage_conjugateStatement D K σ`, by definition `D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K` for a closed subgroup `K` and `σ : G`.

The module opens no namespace and declares no variables: the theorem binds its own `G` and `D`, and none of the source's `open` names or notation occur in it.

## Implemented proof

The proof is the source's after `show` states the published proposition unfolded. `PNat.eq` reduces the equation of positive degrees to the equation of the cardinalities `Nat.card` of the residue quotients of `conjugateClosedSubgroup K.field σ` and of `K.field` (stated with `change`). After unfolding `DegreeData.residueQuotient`, the local fact `himage : D.fieldImage (conjugateClosedSubgroup K.field σ) = D.fieldImage K.field` is the published M027.001 `D.fieldImage_conjugate K.field σ`; the source writes `have himage := D.fieldImage_conjugate K.field σ`, and the port states the unfolded equation as the type of `himage`, since the published theorem's type is the `...Statement` proposition rather than the equation itself. The equation of the degree images gives the equivalence `Subgroup.quotientEquivOfEq` of the two quotients of `ZHatMul` by the degree images (as subgroups of `⊤`), and `Nat.card_congr` concludes. The development check reported only the axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`, lines 66–82](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean#L66-L82):
the docstring at lines 66–67 and the theorem at lines 68–82. It lies in `namespace ClassFormation` (line 17), with `open KummerTheory` (line 19) and `open CyclicCohomology` (line 21), its `noncomputable section` (line 25) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and `{D : DegreeData G} {A : Rep ℤ G}` (lines 28–29). The source passage is:

```lean
/-- Conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
theorem DegreeData.FiniteResidueAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    (K.conjugate σ).residueDegree = K.residueDegree := by
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`;
its SHA-256 is `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement K σ` as its type, and begin the proof with `show` stating it unfolded;
- prove M027.001 `DegreeData.fieldImage_conjugate` as a private theorem by its source proof and use it in place of `D.fieldImage_conjugate K.field σ` (replaced by Worker 743, below);
- omit the source's `open` commands, its variable declarations and all other source declarations.

Modifications by Worker 743 on 16 November 2026:

- the proof of M027.001 is now in the Library, so the module imports its published proof module `...ValuationLaws.FieldImageConjugate.U001.Proofs` and no longer contains the private theorem `fieldImage_conjugate_aux` of Worker 5264's draft;
- the local fact `himage` is the published `D.fieldImage_conjugate K.field σ`, with its unfolded equation stated as its type.

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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M027.003. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
