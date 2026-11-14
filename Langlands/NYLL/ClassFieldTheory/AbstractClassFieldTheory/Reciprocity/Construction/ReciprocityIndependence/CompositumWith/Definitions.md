# NYLL M033.008: the compositum of a finite intermediate field with a field

The paired Lean file ports the definition
`ClassFormation.FiniteIntermediateField.compositumWith` as
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositumWith`. The
source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
(file SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`),
inventory unit M033.008. The definition occupies lines 132–137: the
docstring is at 132–133 and the declaration at 134–137. The section context
is at lines 17–33: `universe u`, `namespace ClassFormation`, the opens
`KummerTheory` and `CyclicCohomology`, `noncomputable section`,
`section groupTheoreticRefinements`, the variables
`{G : Type u} [Group G] [TopologicalSpace G]` and
`namespace FiniteIntermediateField` (closed at line 271). The registered
source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## The definition

Telescope, in the source order and with the source binder kinds: implicit
`{G : Type u}`, instance arguments `[Group G] [TopologicalSpace G]`,
implicit `{E K : ClosedSubgroup G}`, explicit
`(M : FiniteIntermediateField E K)` and explicit `(S : ClosedSubgroup G)`.
The value is the closed subgroup `M.field ⊓ S`, the meet in Mathlib's lattice
of closed subgroups. Fields are represented contravariantly by closed
subgroups, so this intersection `G_M ∩ G_Σ` represents the field compositum
`MΣ`. `FiniteIntermediateField` is M029.001,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField`, ported in
`../../NormSubgroup/Definitions.lean` of this task; `M.field` is its
intermediate-field subgroup.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- The module holds only M033.008. The other declarations of
  `ReciprocityIndependence.lean` are omitted. M033.009 and M033.010, the
  two bounds for `compositumWith`, are statement units of this task; they
  are staged separately, after this module is in the Library, as
  `Statements.lean` of this directory. M033.017 is the statement module
  `../QuotientGenerator/Statements.lean`. The other M033 units are routed
  to a sibling task.
- The module is placed in the subdirectory `ReciprocityIndependence/CompositumWith/`
  so that it does not collide with the sibling task's modules under
  `ReciprocityIndependence/`.
- `open KummerTheory` and `open CyclicCohomology` are omitted: the
  definition uses neither namespace.
- The source imports
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
  are replaced by the focused import of the M029 definitions module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`.

The universe, binders, binder kinds, docstring and body are otherwise
unchanged. A focused `lean_check` of this module reports no errors or
warnings.

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
