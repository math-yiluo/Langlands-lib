# NYLL M017.005–.007: restriction and normalized degree distinguish Frobenius elements

The paired Lean file adapts the statements of three theorems of Naganori
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

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M017.005 | `extensionRestriction_normalizedDegree_joint_injective` | 183–184 | 185–193 | 193–210 | `extensionRestriction_normalizedDegree_joint_injectiveStatement` |
| M017.006 | `frobeniusRestriction_mul` | 212–215 (attribute `@[simp]` line 216) | 217–224 | 224–228 | `frobeniusRestriction_mulStatement` |
| M017.007 | `frobenius_eq_of_restriction_eq_of_degree_eq` | 230–231 | 232–244 | 244–248 | `frobenius_eq_of_restriction_eq_of_degree_eqStatement` |

The source imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup`
and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField`
(lines 7–8) and has the context `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25), the
variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 27) and
`namespace DegreeData` (line 29).

The other declarations of the source file are not part of this module:

- M017.001 `extensionImageInInertiaQuotient` (line 32) and M017.002
  `extensionImageInInertiaQuotient_isClosed` (line 42) are in the separate
  contribution under `FrobeniusDescent/InertiaQuotientImage/`.
- M017.004 `frobeniusFixedField_le_of_restriction_eq_one` (line 137) is
  published as a target in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.FixedFieldLe.Statements`,
  and M017.003 `frobeniusFixedField_le_of_inertia_le_of_lift_mem` (line 76)
  is outside this contribution. None of the three statements mentions them.

The statements use Mathlib's `Function.Injective`, `ClosedSubgroup` with
`toSubgroup`, `Subgroup.Normal`, quotient groups `⧸`, pairs and `Subtype`
projections `.1`, and these published NYLL declarations:

- `Langlands.NYLL.ClassFormation.DegreeData` (M010.002) and
  `DegreeData.FiniteResidueAbstractField` with its field `field` (M010.021);
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), found
  through the source `open CyclicCohomology`;
- `DegreeData.extensionInertiaWithin` (M012.002), with its published
  normality instance `DegreeData.extensionInertiaWithin_normal`, and
  `DegreeData.extensionRestriction` (M012.007), from
  `Degree.FrobeniusLift.Definitions`;
- `DegreeData.extensionNormalizedDegree` (M012.005),
  `DegreeData.FrobeniusElements` (M012.009) and
  `DegreeData.frobeniusRestriction` (M012.010), from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`;
- the instance `DegreeData.frobeniusElementsMul` (M015.002) from
  `Reciprocity.Construction.FrobeniusSemigroup.Definitions`, which supplies
  the product `σ * τ` of Frobenius elements in M017.006. The lexical
  dependency scan did not list it; it was found by elaboration (without the
  import, M017.006 fails to synthesize `HMul`). In the source it reaches
  this file through the import of `FrobeniusSemigroup`.

## Targets and complete telescopes

Each target has, before the binders shown, the binders of the source
variable line 27: implicit `{G : Type*}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

### M017.005

```lean
def extensionRestriction_normalizedDegree_joint_injectiveStatement
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] : Prop :=
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q))
```

On the quotient of `G_K` by the relative inertia `I_L`, the pair consisting
of the restriction to `G(L/K)` and the normalized degree is injective. The
named instance hypothesis `hLnormal` is kept; it is used by instance
resolution in the statement.

### M017.006

```lean
def frobeniusRestriction_mulStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusRestriction K L hLK (σ * τ) =
      D.frobeniusRestriction K L hLK σ *
        D.frobeniusRestriction K L hLK τ
```

The restriction of Frobenius elements is multiplicative for the product
given by the instance `frobeniusElementsMul`.

### M017.007

```lean
def frobenius_eq_of_restriction_eq_of_degree_eqStatement
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) : Prop :=
    σ = τ
```

Two Frobenius elements with the same restriction and the same normalized
degree are equal. The hypotheses `hRestriction` and `hDegree` are kept
although the proposition does not mention them.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation.DegreeData`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proofs are omitted:
   this contribution publishes the proposition targets, and their proofs
   are separate work. The `@[simp]` attribute of M017.006 is omitted
   because the target is a definition of a proposition, not a rewrite rule.
3. Prefix each source docstring with `Target:` (for M017.006 on its own
   line, keeping the source docstring layout) and lower-case the first word
   after it unless it is a name (`Frobenius` in M017.007, code in M017.006);
   the wording is otherwise unchanged, and the lines are rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
4. Replace the two source imports by the focused published imports
   `Degree.FrobeniusLift.FrobeniusElements.Definitions`,
   `Reciprocity.Construction.FrobeniusSemigroup.Definitions`,
   `Degree.Fields.FiniteResidue.Definitions` and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (the first three under
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory`).
5. Omit the other declarations of the source file (listed above). Retain
   the namespaces, the open, the noncomputable section and the variable
   line 27.
6. Precede M017.007 by `set_option linter.unusedVariables false in`: its
   proposition does not mention the hypotheses `hRestriction` and `hDegree`,
   which the linter reports as unused. A check without the option gave
   exactly these two warnings in this module. The option affects only that
   declaration.
7. No helper declaration or instance is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, cup, transfer, Tate or
reciprocity target.

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
