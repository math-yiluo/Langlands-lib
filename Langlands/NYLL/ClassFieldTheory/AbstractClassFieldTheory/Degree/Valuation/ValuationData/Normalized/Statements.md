# NYLL M025.023, M025.024, M025.026 and M025.027: divided-valuation and normalized-valuation targets

The paired Lean file adapts the statements of four theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`.
The pinned source file has SHA-256
`f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M025.023 | `residueDegree_nsmul_dividedAt` | 255–256 | 257–260 | 261–263 | `Langlands.NYLL.ClassFormation.ValuationData.residueDegree_nsmul_dividedAtStatement` |
| M025.024 | `dividedAt_mem_valueGroup` | 265 | 266–269 | 270–284 | `Langlands.NYLL.ClassFormation.ValuationData.dividedAt_mem_valueGroupStatement` |
| M025.026 | `valuationAt_coe` (`@[simp]`, line 293) | 292 | 294–296 | 297 | `Langlands.NYLL.ClassFormation.ValuationData.valuationAt_coeStatement` |
| M025.027 | `normalizedValuation_surjective` | 299–300 | 301–303 | 304–323 | `Langlands.NYLL.ClassFormation.ValuationData.normalizedValuation_surjectiveStatement` |

The enclosing source context is `namespace ClassFormation` (line 19), the
opens of `KummerTheory` and `CyclicCohomology` (lines 21 and 23),
`noncomputable section` (line 27), the comment and group variables at lines
31–32, `namespace ValuationData` (line 177) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` at line 179.

The names used in the statements resolve to published
`Langlands.NYLL` declarations: `ValuationData.dividedAt` and
`ValuationData.valuationAt` (M025.022 and M025.025, from the sibling module
`ValuationData.Normalized.Definitions`), `ValuationData`,
`ValuationData.valueGroup` and `ValuationData.normCompositeAt` (M025.012,
.013 and .019), `KummerTheory.ambientFixedAddSubgroup` (M023.001),
`FiniteAbstractField` (M010.121), `FiniteAbstractField.residueDegree`
(M010.127), `DegreeData` (M010.002), `ZHat` (M008.008) and
`IntegralRepGroupType`. `Function.Surjective`, `Rep`, the coercion from an
`AddSubgroup` to its carrier and the `ℕ`-scalar action are Mathlib's.

## Targets and complete telescopes

Every target has the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit binders shown. The group lies in `Type 0`, and the carrier of
`A` has an arbitrary universe, the single universe parameter. Write `f_K` for
`(K.residueDegree D : ℕ)`, the absolute residue degree of `K` coerced from
`ℕ+`, and `A_K` for `ambientFixedAddSubgroup A K.field`.

```lean
def residueDegree_nsmul_dividedAtStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
  (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a
```

For `a ∈ A_K`, `f_K` times the divided value `(1/f_K) v(N_{K|k} a)` is
`v(N_{K|k} a)`. This is the identity `f_K v_K = v ∘ N_{K|k}` before codomain
restriction.

```lean
def dividedAt_mem_valueGroupStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
  v.dividedAt K a ∈ v.valueGroup
```

For `a ∈ A_K`, the divided value lies in the value group `Z = v(A_k)`.

```lean
def valuationAt_coeStatement (v : ValuationData D A) (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
  (v.valuationAt K a : ZHat) = v.dividedAt K a
```

For `a ∈ A_K`, the normalized valuation `v_K a`, as an element of `ZHat`, is
the divided value of `a`.

```lean
def normalizedValuation_surjectiveStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
  Function.Surjective (v.valuationAt K)
```

The normalized valuation `v_K : A_K → Z` over a finite abstract field `K` is
surjective onto the value group. This is the surjectivity part of the
source's normalized-valuation functoriality.

Binder order and kinds are those of the source theorems. No target has any
further hypothesis.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statement is copied
   verbatim. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Omit the `@[simp]` attribute of `valuationAt_coe`, which cannot apply to
   a proposition-valued definition.
4. Replace each source docstring by a description of the proposition that
   names its source theorem, and replace the source module docstring by a
   description of this module with a modification notice.
5. Replace the source imports by the single focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`.
6. Omit the source's `universe u`, which no target names. Retain both opens,
   the noncomputable section, the group-variable comment and both variable
   lines.
7. Omit all other source units. No helper declaration or instance is added.

These are the exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer, Tate
or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
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
