# NYLL M033.012–.014: finiteness and normality of the compositum with a field

The paired Lean file adapts the statements of the theorems `ClassFormation.FiniteIntermediateField.compositumWith_finite`, `compositumWith_normal` and `compositumWith_finite_over_base` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`.
The pinned source file has SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteIntermediateField.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M033.012 | `compositumWith_finite` | 160 | 161–165 | 165–187 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositumWith_finiteStatement` |
| M033.013 | `compositumWith_normal` | 189 | 190–195 | 195–216 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositumWith_normalStatement` |
| M033.014 | `compositumWith_finite_over_base` | 218–219 | 220–225 | 225–245 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositumWith_finite_over_baseStatement` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`section groupTheoreticRefinements` (line 29), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 31) and
`namespace FiniteIntermediateField` (line 33). The source imports are the
unported modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
(lines 7–8). The definition M033.008 `compositumWith` and the targets
M033.009/.010 `compositumWith_le_left`/`_le_right` are the published modules
`Reciprocity.Construction.ReciprocityIndependence.CompositumWith.{Definitions,Statements}`.
This module is placed in the subdirectory `CompositumWith/Finiteness/` so
that it does not collide with them. The rest of the source file is not part
of this module.

The names used resolve as follows:

- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a structure with a
  closed subgroup `M.field`, `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and the finiteness
  `M.finite` of `K.toSubgroup ⧸ extensionSubgroup K M.field M.below`: an
  intermediate field `E | M | K` finite over `K`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a
  subgroup of `G_K`;
- `FiniteIntermediateField.compositumWith M S` (M033.008, from the published
  module `Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions`),
  the closed subgroup `M.field ⊓ S`, that is `G_M ∩ G_Σ`, representing the
  field compositum `MΣ`.

`ClosedSubgroup`, `Finite`, `Subgroup.Normal` and `inf_le_right` are
Mathlib's; `⧸` is Mathlib's quotient of a group by a subgroup.

## The proof term `M.compositumWith_le_right S`

All three source statements pass `M.compositumWith_le_right S`, the proof
of M033.010 (`compositumWith_le_right`, source lines 146–151, proof
`inf_le_right` at line 151), as the third argument of `extensionSubgroup`.
The statement of M033.010 is published (as `compositumWith_le_rightStatement`)
but its proof is not. Each target writes the source proof instead, as
`show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from inf_le_right`, a
term of the same type `(M.compositumWith S).toSubgroup ≤ S.toSubgroup`. The
third argument of `extensionSubgroup` is a proof of a proposition, so by
proof irrelevance each target is the same proposition as the source
statement, whatever proof of M033.010 is published later.

## Targets and complete telescopes

All three targets have the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by those shown. Each is preceded by
`set_option linter.unusedVariables false in`, explained under
Modifications.

### M033.012

```lean
def compositumWith_finiteStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup) : Prop :=
  Finite (S.toSubgroup ⧸
      extensionSubgroup S (M.compositumWith S)
        (show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from inf_le_right))
```

For a finite intermediate field `M` of `E | K` and a closed subgroup `G_Σ`
of `G_K`, `G_M ∩ G_Σ` has finite index in `G_Σ`: the compositum `MΣ` is
finite over `Σ`. The source statement differs only by the proof term.

### M033.013

```lean
def compositumWith_normalStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hMnormal : (extensionSubgroup K M.field M.below).Normal] : Prop :=
  (extensionSubgroup S (M.compositumWith S)
      (show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from
        inf_le_right)).Normal
```

If moreover `G_M` is normal in `G_K`, then `G_M ∩ G_Σ` is normal in `G_Σ`:
the compositum of a Galois extension `M | K` with `Σ` is Galois over `Σ`.
The source statement differs only by the proof term.

### M033.014

```lean
def compositumWith_finite_over_baseStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hSfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] : Prop :=
  Finite (K.toSubgroup ⧸ extensionSubgroup K (M.compositumWith S)
      ((show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from
        inf_le_right).trans hSK))
```

If moreover `G_Σ` has finite index in `G_K`, then `G_M ∩ G_Σ` has finite
index in `G_K`: the compositum `MΣ` is finite over `K`. The source writes
the inclusion as `(M.compositumWith_le_right S).trans hSK`; the target
writes `(show … from inf_le_right).trans hSK`, which differs only by the
proof term.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes are copied
   verbatim; in each statement the proof term `M.compositumWith_le_right S`
   is replaced by the inline source proof, as explained above, and the
   lines are rewrapped. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorems.
4. Replace the source imports by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions`
   (M033.008, which also brings M029.001 and M004.002).
5. Omit the other declarations of the source file and the unused
   `open KummerTheory`. Retain `universe u`, `open CyclicCohomology` (for
   `extensionSubgroup`), the noncomputable section, the section
   `groupTheoreticRefinements`, its variable line and the namespaces.
6. Precede each target by `set_option linter.unusedVariables false in`. The
   source binders `hSK` (in M033.012 and M033.013), `hMnormal` (M033.013)
   and `hSfinite` (M033.014) are used by the source proofs but not by the
   statements, so without the option the linter warns about them in the
   Prop-valued definitions. The binders are kept so that the telescopes are
   the source's.
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
