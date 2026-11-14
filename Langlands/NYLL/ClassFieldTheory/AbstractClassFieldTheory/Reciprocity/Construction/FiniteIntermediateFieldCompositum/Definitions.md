# NYLL M037.001: the quotient cardinality of a finite intermediate field

The paired Lean file ports the definition
`ClassFormation.FiniteIntermediateField.quotientCard` as
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.quotientCard`. The
source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`
(file SHA-256
`924ba9423c5c9c4fc389345e02f552dc93d98f2c87114448f72f841a0085e2ec`),
inventory unit M037.001. The definition occupies lines 36–45: the docstring
is at 36–39 and the declaration at 40–45. The section context is at lines
16–34: `universe u v`, `namespace ClassFormation`, the opens `KummerTheory`
and `CyclicCohomology`, `noncomputable section`, `open CategoryTheory`,
`open scoped BigOperators`, `section finiteIntermediateFields`, the variables
`{G : Type u} [Group G] [TopologicalSpace G]` and
`namespace FiniteIntermediateField` (closed at line 77). The registered
source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## The definition

Telescope, in the source order and with the source binder kinds: implicit
`{G : Type u}`, instance arguments `[Group G] [TopologicalSpace G]`,
implicit `{E K : ClosedSubgroup G}` and explicit
`(M : FiniteIntermediateField E K)`. The value is a natural number. It is
defined, as in the source, by the tactic block

```lean
  letI : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card
    (K.toSubgroup ⧸ extensionSubgroup K M.field M.below)
```

So `quotientCard M` is `Nat.card (G_K / G_M)`, the number of cosets of the
intermediate-field subgroup `G_M` in `G_K`, that is, the degree `[M : K]`.
The local `Finite` instance comes from the structure field `M.finite`.
`Nat.card` itself does not need the instance, so the value is
`Nat.card (G_K / G_M)` in any case; as the source docstring says, the
instance is recorded only for later fixed-field constructions.
`FiniteIntermediateField` is M029.001,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField`, ported in
`../NormSubgroup/Definitions.lean` of this task. `extensionSubgroup` is the
Library's `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`, reached by name
through `open CyclicCohomology` as in the source.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- The module holds only M037.001. M037.002 and M037.003 are statement units
  of this task; they are staged separately, after this module is in the
  Library, as `Statements.lean` of this directory.
- `universe u v` becomes `universe u`: the definition does not use `v`,
  which appears only in M037.003.
- `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`
  are omitted: the definition uses none of them. `open CyclicCohomology` is
  kept for `extensionSubgroup`.
- The source import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm`
  is replaced by the focused import of the M029 definitions module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`.

The universe `u`, binders, binder kinds, the `noncomputable` modifier, the
docstring and the body are otherwise unchanged. A focused `lean_check` of
this module reports no errors or warnings and the single universe parameter
`u`.

## Scope

This is a data definition only. No reciprocity, class-formation or
cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
