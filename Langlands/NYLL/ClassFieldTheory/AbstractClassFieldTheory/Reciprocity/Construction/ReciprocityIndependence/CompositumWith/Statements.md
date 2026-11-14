# NYLL M033.009–010: targets for the two compositum bounds

The paired Lean file gives two Prop-valued targets for the source theorems
`ClassFormation.FiniteIntermediateField.compositumWith_le_left` and
`ClassFormation.FiniteIntermediateField.compositumWith_le_right`. The source
is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
(file SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`). The
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
| M033.009 | `compositumWith_le_left` | 139–144 (theorem at 140) | `compositumWith_le_leftStatement` |
| M033.010 | `compositumWith_le_right` | 146–151 (theorem at 147) | `compositumWith_le_rightStatement` |

The section context is at source lines 17–33: `universe u`,
`namespace ClassFormation`, the opens `KummerTheory` and `CyclicCohomology`,
`noncomputable section`, `section groupTheoreticRefinements`, the variables
`{G : Type u} [Group G] [TopologicalSpace G]` and
`namespace FiniteIntermediateField` (closed at line 271).

## The targets

Both targets have the source telescope: implicit `{G : Type u}`, instance
arguments `[Group G] [TopologicalSpace G]`, implicit
`{E K : ClosedSubgroup G}`, explicit `(M : FiniteIntermediateField E K)` and
explicit `(S : ClosedSubgroup G)`. A field is represented contravariantly by
a closed subgroup of `G`, Mathlib's `ClosedSubgroup G`; a larger field has a
smaller subgroup. `FiniteIntermediateField` is M029.001,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField`, ported in
`../../NormSubgroup/Definitions.lean` of this task; `M.field` is the
subgroup `G_M` of the finite intermediate field `M` of `E | K`.
`M.compositumWith S` is M033.008,
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.compositumWith`,
ported in `Definitions.lean` of this directory: the closed subgroup
`M.field ⊓ S`, i.e. `G_M ∩ G_Σ`, which represents the field compositum `MΣ`.

Each body is the source conclusion verbatim.

**M033.009** `compositumWith_le_leftStatement` has the body

```lean
(M.compositumWith S).toSubgroup ≤ M.field.toSubgroup
```

so `G_M ∩ G_Σ ≤ G_M`: the compositum `MΣ` contains `M`.

**M033.010** `compositumWith_le_rightStatement` has the body

```lean
(M.compositumWith S).toSubgroup ≤ S.toSubgroup
```

so `G_M ∩ G_Σ ≤ G_Σ`: the compositum `MΣ` contains `Σ`.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to each name. Each `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The proofs (`inf_le_left` and `inf_le_right`) are not ported. Proving the
  targets is separate `lean.proof@1` work.
- The docstrings are prefixed with "Target:"; their wording is otherwise the
  source wording.
- The module holds only these two targets, in the subdirectory
  `ReciprocityIndependence/CompositumWith/` beside the M033.008 definition,
  so that it does not collide with the sibling task's modules under
  `ReciprocityIndependence/`. The other declarations of the source module
  are omitted.
- `open KummerTheory` and `open CyclicCohomology` are omitted: the targets
  use neither namespace. `universe u`, `noncomputable section`, the section,
  the variable line and `namespace FiniteIntermediateField` are kept.
- The source imports
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
  are replaced by the single focused import
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions`,
  which provides `compositumWith` and, through its own import,
  `FiniteIntermediateField`.

The universe `u`, binders, binder kinds and their order, and the bodies are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings; each target returns `Prop` and has the single universe
parameter `u`.

## Scope

This unit states M033.009 and M033.010 and proves neither. No reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
