# NYLL M025.018 and M025.020: value-reduction surjectivity and norm-composite range targets

The paired Lean file adapts the statements of two theorems from Naganori
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
No NYLL-specific erratum was found among the available project errata notes.

## Source correspondence

| Unit | Source theorem | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M025.018 | `ClassFormation.ValuationData.valueModulo_surjective` | 212 | 213–215 | 215–220 | `Langlands.NYLL.ClassFormation.ValuationData.valueModulo_surjectiveStatement` |
| M025.020 | `ClassFormation.ValuationData.normCompositeAt_range` | 227 | 228–230 | 231 | `Langlands.NYLL.ClassFormation.ValuationData.normCompositeAt_rangeStatement` |

The enclosing source context is `namespace ClassFormation` (line 19),
`noncomputable section` (line 27), the comment and group variables at lines
31–32, `namespace ValuationData` (line 177) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` at line 179.

The names used in the statements resolve to the published
`Langlands.NYLL.ClassFormation` declarations `ValuationData`,
`ValuationData.valueModulo`, `ValuationData.normCompositeAt` and
`ValuationData.valueGroup` (M025.012, .016, .019 and .013, from the paired
`ValuationData.Definitions` module), `nsmulImage` (M025.004),
`FiniteAbstractField` (M010.121), `FiniteAbstractField.residueDegree`
(M010.127), `DegreeData` (M010.002) and `ZHat` (M008.008), and to
`Langlands.NYLL.IntegralRepGroupType`. `Function.Surjective`,
`AddMonoidHom.range`, `Rep` and `ZMod` are Mathlib's.

## Targets and complete telescopes

Both targets have the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit `v : ValuationData D A`. The group lies in `Type 0`; the carrier
of `A` has an arbitrary universe, the single universe parameter.

```lean
def valueModulo_surjectiveStatement (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) : Prop :=
  Function.Surjective (v.valueModulo n hn)
```

For every positive natural number `n`, reduction of the value group
`Z = v(A_k)` modulo `n` (the quotient projection to `Z / nZ` followed by
the canonical equivalence with `ZMod n`) is surjective. The positivity
hypothesis `hn` is used in the statement, as an argument of `valueModulo`.

```lean
def normCompositeAt_rangeStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
  (v.normCompositeAt K).range =
    nsmulImage v.valueGroup (K.residueDegree D : ℕ)
```

For a field `K` finite over the distinguished base field `k`, the range of
`v ∘ N_{K|k}` on `A_K` equals the image of the value group under
multiplication by the absolute residue degree `f_K` (an `ℕ+` coerced to
`ℕ`). This is the structure field `norm_range` stated through the derived
definitions `normCompositeAt` and `valueGroup`.

Binder order and kinds are those of the source theorems. Neither target has
any further hypothesis.

## Modification record

Worker 110 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statement is copied
   verbatim. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Replace each source docstring (lines 212 and 227) by a description of the
   proposition that names its source theorem, and replace the source module
   docstring by a description of this module with a modification notice.
4. Replace the source imports by the single focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`.
5. Omit the source's `open KummerTheory`, `open CyclicCohomology` and
   `universe u`, which neither target uses. Retain the noncomputable section,
   the group-variable comment and both variable lines.
6. Omit all other source units, including M025.017 (`valueModulo_apply`).
   No helper declaration or instance is added.

These are the exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer, Tate
or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with no errors or warnings.
Declaration inspection of both targets reported
`statement_returns_prop: true`, one universe parameter, and the axioms
`propext`, `Classical.choice` and `Quot.sound`. A private probe assigned each
unapplied target to its full expected telescope at an arbitrary carrier
universe `u` and checked by reflexivity that each body is exactly the source
statement. Compilation and inspection are separate from independent semantic
acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
