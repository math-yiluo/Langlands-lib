# NYLL M034.002–.003: the compositum lies below both finite intermediate fields

The paired Lean file adapts the statements of the theorems `ClassFormation.FiniteIntermediateField.compositum_le_left` and `compositum_le_right` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`.
The pinned source file has SHA-256
`579d38da784d715ecd9a49a310408856e4235252d3b5940440f7b17684c303b1`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteIntermediateField.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M034.002 | `compositum_le_left` | 42 | 43–45 | 45–46 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositum_le_leftStatement` |
| M034.003 | `compositum_le_right` | 48 | 49–51 | 51–52 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositum_le_rightStatement` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open CyclicCohomology` (line 19), `noncomputable section` (line 23), the
variables `{G : Type*} [Group G] [TopologicalSpace G]` (line 25) and
`namespace FiniteIntermediateField` (line 27). The source import is the
unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence`
(line 7). The definition M034.001 `compositum` is in the sibling module
`Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions`.
The rest of the source file is not part of this module.

The names used resolve as follows:

- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a structure with a
  closed subgroup `M.field` lying between `G_E` and `G_K` with finite
  relative quotient: an intermediate field `E | M | K` finite over `K`;
- `FiniteIntermediateField.compositum M N` (M034.001, from the sibling
  module `Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions`),
  the finite intermediate field whose closed subgroup is
  `M.field ⊓ N.field`.

`ClosedSubgroup` is Mathlib's.

## Targets and complete telescopes

Both targets have the binders implicit `{G : Type*}`, `[Group G]` and
`[TopologicalSpace G]`, followed by those shown.

### M034.002

```lean
def compositum_le_leftStatement {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) : Prop :=
  (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup
```

`G_M ∩ G_N ≤ G_M`: the compositum `MN` contains `M`.

### M034.003

```lean
def compositum_le_rightStatement {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) : Prop :=
  (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup
```

`G_M ∩ G_N ≤ G_N`: the compositum `MN` contains `N`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim. The source proofs (`inf_le_left` and
   `inf_le_right`) are omitted: this contribution publishes the proposition
   targets, and their proofs are separate work.
3. Each source docstring reads ``Proves the bound `…`.``; the verb `Proves`
   is replaced by `Target: the`, and the line is rewrapped. The quoted
   bound is unchanged. Replace the source module docstring by a
   description of this module with a modification notice that names the
   source theorems.
4. Replace the source import by the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions`
   of this contribution (M034.001, which also brings M033.008, M029.001 and
   M004.002).
5. Omit the other declarations of the source file and the unused
   `open CyclicCohomology`. Retain the noncomputable section, the variable
   line and the namespaces. Every binder occurs in its proposition, so no
   linter option is needed.
6. No helper declaration or instance is added.

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
