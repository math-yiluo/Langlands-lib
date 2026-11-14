# NYLL M037.002–003: positivity and common composita of finite stages

The paired Lean file gives two Prop-valued targets for the source theorems
`ClassFormation.FiniteIntermediateField.quotientCard_pos` and
`ClassFormation.FiniteIntermediateField.exists_common_compositum`. The source
is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`
(file SHA-256
`924ba9423c5c9c4fc389345e02f552dc93d98f2c87114448f72f841a0085e2ec`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.`. Original names use
the prefix `ClassFormation.FiniteIntermediateField.`. The line ranges include
the docstrings.

| Unit | Original theorem | Source lines | Adapted target |
| --- | --- | --- | --- |
| M037.002 | `quotientCard_pos` | 47–52 (theorem at 48) | `quotientCard_posStatement` |
| M037.003 | `exists_common_compositum` | 54–75 (theorem at 57) | `exists_common_compositumStatement` |

The section context is at source lines 16–34: `universe u v`,
`namespace ClassFormation`, the opens `KummerTheory` and `CyclicCohomology`,
`noncomputable section`, `open CategoryTheory`, `open scoped BigOperators`,
`section finiteIntermediateFields`, the variables
`{G : Type u} [Group G] [TopologicalSpace G]` and
`namespace FiniteIntermediateField` (closed at line 77).

## The targets

A field is represented contravariantly by a closed subgroup of `G`,
Mathlib's `ClosedSubgroup G`; a larger field has a smaller subgroup.
`FiniteIntermediateField E K` is M029.001,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField`, ported in
`../NormSubgroup/Definitions.lean` of this task: a closed subgroup
`field = G_M` with `G_E ≤ G_M ≤ G_K` and finite coset space `G_K / G_M`,
i.e. a finite intermediate field `M` of `E | K`.

Each body is the source conclusion verbatim.

**M037.002** `quotientCard_posStatement` has the telescope implicit
`{G : Type u}`, instance arguments `[Group G] [TopologicalSpace G]`,
implicit `{E K : ClosedSubgroup G}` and explicit
`(M : FiniteIntermediateField E K)`. Its body is

```lean
0 < M.quotientCard
```

`M.quotientCard` is M037.001,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.quotientCard`, ported
in `Definitions.lean` of this directory: the natural number
`Nat.card (G_K / G_M)`, the degree `[M : K]`. The target says that this
degree is positive. (`Nat.card` is `0` for an infinite type, so this uses the
finiteness carried by `M`.)

**M037.003** `exists_common_compositumStatement` has the telescope implicit
`{G : Type u}`, instance arguments `[Group G] [TopologicalSpace G]`,
implicit `{E K : ClosedSubgroup G}`, implicit `{ι : Type v}`, explicit
`(M : FiniteIntermediateField E K)`, explicit `(s : Finset ι)` and explicit
`(F : ι → FiniteIntermediateField E K)`. Its body is

```lean
∃ P : FiniteIntermediateField E K,
  P.field.toSubgroup ≤ M.field.toSubgroup ∧
    ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup
```

It says that for a finite intermediate field `M` and a finite family
`(F i)_{i ∈ s}` of finite intermediate fields of `E | K`, there is a finite
intermediate field `P` of `E | K` whose subgroup lies below `G_M` and below
every `G_{F i}` with `i ∈ s`; that is, `P` contains `M` and every `F i`.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to each name. Each `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The proofs (lines 50–52 and 63–75, after the signatures that end with
  `:= by` at lines 49 and 62) are not ported. Proving the targets is
  separate `lean.proof@1` work. The source proof of M037.003 uses
  `FiniteIntermediateField.compositum` and its two bounds from
  `FiniteIntermediateCompositum.lean`, which are not needed to state the
  target.
- The docstrings are prefixed with "Target:"; their wording is otherwise the
  source wording.
- The module holds only these two targets. M037.001 is in `Definitions.lean`
  of this directory, which this module imports.
- `open KummerTheory`, `open CyclicCohomology`, `open CategoryTheory` and
  `open scoped BigOperators` are omitted: the targets use none of them.
  `universe u v`, `noncomputable section`, the section, the variable line and
  `namespace FiniteIntermediateField` are kept.
- The source import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm`
  is replaced by the single focused import
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.Definitions`,
  which provides `quotientCard` and, through its own import,
  `FiniteIntermediateField`.

The universes, binders, binder kinds and their order, and the bodies are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings; both targets return `Prop`. `quotientCard_posStatement` has the
single universe parameter `u` and `exists_common_compositumStatement` has
the universe parameters `u v`.

## Scope

This unit states M037.002 and M037.003 and proves neither. No norm-descent,
reciprocity, class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
