# NYLL M027.002: the conjugate of a residue-finite abstract field

The paired Lean file adapts one definition of Naganori
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

| Unit | Source definition after `ClassFormation.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- |
| M027.002 | `DegreeData.FiniteResidueAbstractField.conjugate` | 53–55 | 56–59 | 60–64 | `DegreeData.FiniteResidueAbstractField.conjugate` |

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

The definition binds its own `{G : Type*} [Group G] [TopologicalSpace G]
{D : DegreeData G}`, so it uses neither the variable lines nor the two
opens. The port keeps `namespace` and `noncomputable section` and omits the
opens, the comment and the variable lines. The definition has one universe
parameter, that of `G`.

The names used resolve to published `Langlands.NYLL.ClassFormation`
declarations: the structure `DegreeData.FiniteResidueAbstractField D`
(M010.021, in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`) of a closed
subgroup `field` with `finiteResidueQuotient : Finite (D.residueQuotient field)`;
`DegreeData` (M010.002), the degree image `DegreeData.fieldImage` (M010.010)
and the residue quotient `DegreeData.residueQuotient K`, the quotient of
`⊤ : Subgroup ZHatMul` by `(D.fieldImage K).subgroupOf ⊤` (M010.018), all in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`; the conjugate closed subgroup
`conjugateClosedSubgroup K σ` with underlying subgroup
`ConjAct.toConjAct σ⁻¹ • K.toSubgroup` (M026.001, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`); and the published theorems
`DegreeData.fieldImage_eq_map` (M010.011, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs`), whose type is the published target
`DegreeData.fieldImage_eq_mapStatement D K`, the equation
`D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom`, and
`conjugateClosedSubgroup_mem` (M026.002, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`), whose type is the published target
`conjugateClosedSubgroup_memStatement K σ x`, the equivalence
`x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K`. Mathlib supplies
`ClosedSubgroup`, `ContinuousMul`, `Subgroup.map`, `Finite`, `map_mul`,
`mul_assoc` and `mul_comm`.

The source proof of the field `finiteResidueQuotient` rewrites with
`D.fieldImage_conjugate K.field σ`, the theorem M027.001
`DegreeData.fieldImage_conjugate` (lines 31–51):
`D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K`. Its statement
is published as `Langlands.NYLL.ClassFormation.DegreeData.fieldImage_conjugateStatement` (in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.Statements`), but its proof
is not. The port proves that equation at `K.field` as a local `himage`
inside the field proof, by the source proof of lines 36–51 with three
changes forced by the published Statement types:

- the source `rw [D.fieldImage_eq_map, D.fieldImage_eq_map]` is replaced by
  local hypotheses `hKσ` and `hK`, stating exactly the two instances of the
  equation of M010.011 at `conjugateClosedSubgroup K.field σ` and at
  `K.field` and proved by the published theorem, followed by
  `rw [hKσ, hK]`; `rw` does not unfold the published `...Statement` type;
- the source uses `(conjugateClosedSubgroup_mem K σ x).mp hx` and
  `rw [conjugateClosedSubgroup_mem]`; the port states the equivalence of
  M026.002 for all `x` as a local `hmem`, proved by the published theorem,
  and uses `(hmem x).mp hx` and `rw [hmem]`;
- `K` of the source theorem becomes `K.field`.

The remaining tactic lines are the source's. The field proof then continues
exactly as in the source, `unfold DegreeData.residueQuotient`,
`rw [himage]` (for the source `rw [D.fieldImage_conjugate K.field σ]`) and
`exact K.finiteResidueQuotient`. The field is a proof of a proposition, so
by proof irrelevance the structure value is the source one.

## Definition

```lean
/-- Conjugate a field whose actual absolute residue quotient is finite.
The transported field remains in the same residue-finite boundary because
conjugation does not change the degree image. -/
noncomputable def DegreeData.FiniteResidueAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField D where
  field := conjugateClosedSubgroup K.field σ
  finiteResidueQuotient := by
    have himage : D.fieldImage (conjugateClosedSubgroup K.field σ) =
        D.fieldImage K.field := by
      have hKσ : D.fieldImage (conjugateClosedSubgroup K.field σ) =
          (conjugateClosedSubgroup K.field σ).toSubgroup.map
            D.degree.toMonoidHom :=
        D.fieldImage_eq_map (conjugateClosedSubgroup K.field σ)
      have hK : D.fieldImage K.field =
          K.field.toSubgroup.map D.degree.toMonoidHom :=
        D.fieldImage_eq_map K.field
      have hmem : ∀ x : G, x ∈ conjugateClosedSubgroup K.field σ ↔
          σ * x * σ⁻¹ ∈ K.field :=
        fun x => conjugateClosedSubgroup_mem K.field σ x
      rw [hKσ, hK]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        let k : K.field.toSubgroup :=
          ⟨σ * x * σ⁻¹, (hmem x).mp hx⟩
        refine ⟨k.1, k.2, ?_⟩
        simp [k, map_mul, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        let x : G := σ⁻¹ * k * σ
        have hx : x ∈ conjugateClosedSubgroup K.field σ := by
          rw [hmem]
          change σ * x * σ⁻¹ ∈ K.field.toSubgroup
          simpa [x, mul_assoc] using hk
        refine ⟨x, hx, ?_⟩
        simp [x, map_mul, mul_assoc, mul_comm]
    unfold DegreeData.residueQuotient
    rw [himage]
    exact K.finiteResidueQuotient
```

For a residue-finite abstract field `K` and `σ ∈ G`, the definition is the
residue-finite field with closed subgroup `σ⁻¹ G_K σ`. Its residue quotient
is finite because conjugation does not change the degree image: the degree
of `σ x σ⁻¹` is that of `x`, since `ZHatMul` is commutative.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.conjugate`.
2. In the proof of the field `finiteResidueQuotient`, insert the local
   `himage` described above before `unfold DegreeData.residueQuotient`, and
   replace `rw [D.fieldImage_conjugate K.field σ]` by `rw [himage]`.
3. Copy the docstring, the modifier `noncomputable`, the binders, the field
   `field` and the other proof lines verbatim; a line diff against the
   pinned source (lines 53–64 and, for `himage`, lines 36–51) shows only the
   changes listed here.
4. Replace the two source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs` and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`, which import the modules of all
   names listed above, and the source module docstring by a description of
   this module with a modification notice.
5. Omit the two opens, the comment and the variable lines, which the
   definition does not use, and the other declarations of the source file,
   including M027.001. No helper declaration, instance or linter option is
   added.

This is a definition only. It discharges no host class-formation, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
