# NYLL M028.009–M028.012: units, unramified inclusions and prime elements

The paired Lean file adapts the statements of four theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`.
The pinned source file has SHA-256
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M028.009 | `mem_unitAddSubgroup_iff` (`@[simp]`, line 133) | 132 | 134–137 | 138 | `Langlands.NYLL.ClassFormation.ValuationData.mem_unitAddSubgroup_iffStatement` |
| M028.010 | `valuationAt_fixedFieldInclusion_of_unramified` | 140–141 | 142–149 | 150–180 | `Langlands.NYLL.ClassFormation.ValuationData.valuationAt_fixedFieldInclusion_of_unramifiedStatement` |
| M028.011 | `prime_of_unramified` | 182 | 183–189 | 190–192 | `Langlands.NYLL.ClassFormation.ValuationData.prime_of_unramifiedStatement` |
| M028.012 | `norm_prime_of_totallyRamified` | 194 | 195–201 | 202–214 | `Langlands.NYLL.ClassFormation.ValuationData.norm_prime_of_totallyRamifiedStatement` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), the comment and variables at lines 26–28,
and `namespace ValuationData` (line 107).

The names used in the statements resolve to published `Langlands.NYLL`
declarations: `ClassFormation.ValuationData.IsPrimeElement` and
`ClassFormation.ValuationData.unitAddSubgroup` (M028.007 and M028.008, from
the sibling module `Degree.PrimeElements.Prime.Definitions`),
`ClassFormation.ValuationData` (M025.012),
`ClassFormation.ValuationData.valuationAt` (M025.025),
`ClassFormation.fixedFieldInclusion` (M028.001, in
`Degree.PrimeElements.Definitions`), `ClassFormation.relativeNorm`
(M024.009, in `Degree.Norm.RelativeNorm.Definitions`), whose `Finite`
quotient argument is supplied by the published instance
`PortInternal.M010.d139` (M010.139),
`ClassFormation.FiniteAbstractFieldExtension` (M010.130) with its fields
`field`, `base` and `below`,
`ClassFormation.FiniteAbstractFieldExtension.IsUnramified` (M010.133) and
`ClassFormation.FiniteAbstractFieldExtension.IsTotallyRamified` (M010.134),
both in `Degree.Fields.FiniteAbstractField.Extension.Definitions`,
`ClassFormation.FiniteAbstractField` (M010.121), `ClassFormation.DegreeData`
(M010.002), `KummerTheory.ambientFixedAddSubgroup` (M023.001) and
`IntegralRepGroupType` (M002.001). The numeral `0` of the value group, `↔`,
`→` and `Rep` are Lean's or Mathlib's.

## Targets and complete telescopes

Every target has the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit binders shown. The group lies in `Type 0`; the carrier of `A`
has an arbitrary universe, the single universe parameter. Write
`A_K = ambientFixedAddSubgroup A K.field`. For
`E : FiniteAbstractFieldExtension G`, the top field is `L = E.field`, the base
field is `K = E.base`, and `E.below` is the containment `G_L ≤ G_K`;
`fixedFieldInclusion A E.base.field E.field.field E.below : A_K →+ A_L` is
the inclusion of fixed modules and
`relativeNorm A E.base.field E.field.field E.below : A_L →+ A_K` is the norm
`N_{L|K}`, the sum over coset representatives of `G_K / G_L`.

```lean
def mem_unitAddSubgroup_iffStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) : Prop :=
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0
```

An element `u ∈ A_K` lies in the additive unit group `U_K` exactly when its
normalized valuation is `0` in the value group.

```lean
set_option linter.unusedVariables false in
def valuationAt_fixedFieldInclusion_of_unramifiedStatement
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) : Prop :=
    v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below a) =
      v.valuationAt E.base a
```

If `L | K` is unramified, then for `a ∈ A_K` the normalized valuation of `L`
at the image of `a` in `A_L` is the normalized valuation of `K` at `a`.

```lean
set_option linter.unusedVariables false in
def prime_of_unramifiedStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (π : ambientFixedAddSubgroup A E.base.field)
    (hπ : v.IsPrimeElement E.base π) : Prop :=
    v.IsPrimeElement E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below π)
```

If `L | K` is unramified and `π` is a prime element of `K`, then its image in
`A_L` is a prime element of `L`.

```lean
set_option linter.unusedVariables false in
def norm_prime_of_totallyRamifiedStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (π : ambientFixedAddSubgroup A E.field.field) : Prop :=
    v.IsPrimeElement E.field π →
      v.IsPrimeElement E.base
        (relativeNorm A E.base.field E.field.field E.below π)
```

If `L | K` is totally ramified, then the norm `N_{L|K} π` of a prime element
`π` of `L` is a prime element of `K`. As in the source, the primality of `π`
is the antecedent of an implication inside the proposition, not a binder.

Binder names, order and kinds are those of the source theorems. The
hypotheses `hUn`, `hπ` and `hTot` are explicit binders of the targets; they
are not mentioned in the propositions, exactly as in the source, where they
are used only by the proofs. A prover of the target receives them as
hypotheses.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statement is copied
   verbatim. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Omit the `@[simp]` attribute of `mem_unitAddSubgroup_iff`, which cannot
   apply to a proposition-valued definition.
4. Precede M028.010, M028.011 and M028.012 by
   `set_option linter.unusedVariables false in`. Without it, Lean's
   unused-variables linter warns about the hypothesis binders that the
   propositions do not mention. The option affects only the linter and keeps
   the source binder names; it changes no term.
5. Replace each source docstring by a description of the proposition that
   names its source theorem, and replace the source module docstring by a
   description of this module with a modification notice.
6. Replace the source import of `Degree.ValuationLaws` by the focused imports
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`
   and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`.
7. Retain both opens, the noncomputable section, the group-variable comment
   and both variable lines. Omit all other source units. No helper
   declaration or instance is added.

These are the exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection reported `statement_returns_prop: true`, one universe
parameter and the axioms `propext`, `Classical.choice` and `Quot.sound` for
each target. Compilation and inspection are separate from independent
semantic acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
