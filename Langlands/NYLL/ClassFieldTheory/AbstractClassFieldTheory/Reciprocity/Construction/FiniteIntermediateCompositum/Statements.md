# NYLL M034.004: finite intermediate fields of a finite field are finite

The paired Lean file gives the Prop-valued target
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.absoluteFiniteStatement`
for the source theorem `ClassFormation.FiniteIntermediateField.absoluteFinite`.
The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`
(file SHA-256
`579d38da784d715ecd9a49a310408856e4235252d3b5940440f7b17684c303b1`),
inventory unit M034.004. The theorem occupies lines 54–65: the docstring is
at 54–55, the signature at 56–61 (ending with `:= by`) and the proof at
62–65. The context is at lines 17–27: `namespace ClassFormation`,
`open CyclicCohomology`, `noncomputable section`, the variables
`{G : Type*} [Group G] [TopologicalSpace G]` and
`namespace FiniteIntermediateField` (closed at line 67). The source file has
no `universe` command. The registered source
`external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## The statement

A field is represented contravariantly by a closed subgroup of `G`,
Mathlib's `ClosedSubgroup G`; a larger field has a smaller subgroup. The
parameters are, in the source order and with the source binder kinds:

- implicit `G : Type*` (a universe variable, `u_1` after elaboration) and
  instance arguments `[Group G]` and `[TopologicalSpace G]`, from the
  section variables;
- implicit `E K : ClosedSubgroup G`, the subgroups `G_E` and `G_K` of the top
  field `E` and the base field `K`;
- instance argument
  `[_hKfinite : Finite ((baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) K (le_baseField K))]`
  (source name `hKfinite`): the coset space `G / G_K` is finite, so `K` has
  finite degree over the distinguished base field;
- explicit `M : FiniteIntermediateField E K`, a finite intermediate field of
  `E | K`.

The body, which is the source conclusion verbatim, is

```lean
Finite ((baseField G).toSubgroup ⧸
    extensionSubgroup (baseField G) M.field (le_baseField M.field))
```

It says that the coset space `G / G_M` is finite: `M` has finite degree over
the distinguished base field.

The declarations used are these.

- `FiniteIntermediateField` is M029.001,
  `Langlands.NYLL.ClassFormation.FiniteIntermediateField`, ported in
  `../NormSubgroup/Definitions.lean` of this task. Its fields include
  `field : ClosedSubgroup G` (the subgroup `G_M`) with `E ≤ field ≤ K` and
  finiteness of `G_K / G_M`.
- `baseField G` is the Library's `Langlands.NYLL.ClassFormation.baseField`
  (M010.003), the closed subgroup `⊤`, i.e. the whole group `G`; it
  represents the distinguished base field.
- `le_baseField` is the Library's
  `Langlands.NYLL.ClassFormation.le_baseField` (M010.005), the proof that
  `K.toSubgroup ≤ (baseField G).toSubgroup` for every closed subgroup `K`.
  In the Library its type is written `le_baseFieldStatement K`, a
  Prop-valued definition whose body is exactly
  `K.toSubgroup ≤ (baseField G).toSubgroup`; Lean unfolds it when the
  proof is passed to `extensionSubgroup`. Only the proof's type matters
  here, and it is the source type.
- `extensionSubgroup` is the Library's
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`, i.e. `G_L` viewed
  as a subgroup of `G_K`; its proof argument is not used by its body. It is
  reached by name through `open CyclicCohomology`, as in the source. No
  normality is assumed, so `⧸` is the coset space.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to the name. The `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The instance argument name `hKfinite` becomes `_hKfinite`, because the body
  does not refer to it (Lean's unused-variable linter otherwise warns). The
  parameter keeps its position, instance binder kind and full type, so a
  proof of the target takes it in the source order.
- The proof (lines 62–65, through `relativeTowerQuotientFinite`) is not
  ported. Proving the target is separate `lean.proof@1` work.
- The docstring is prefixed with "Target:"; its wording is otherwise the
  source wording.
- The module holds only this target. The other declarations of the source
  module (`compositum`, `compositum_le_left` and `compositum_le_right`, lines
  29–52) are not units of this task and are omitted; the target does not
  use them.
- `variable {G : Type*}`, `open CyclicCohomology` and `noncomputable section`
  are kept; as in the source there is no `universe` command.
- The source import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence`
  is replaced by the focused imports
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`
  (for `FiniteIntermediateField` and, through its imports, `baseField` and
  `extensionSubgroup`) and
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`
  (for `le_baseField`).

The binders, binder kinds and their order, and the body are otherwise
unchanged. A focused `lean_check` of this module reports no errors or
warnings; the target returns `Prop` and has the single universe parameter
`u_1`.

## Scope

This unit states M034.004 and does not prove it. No reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
