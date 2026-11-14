# NYLL M026.002: membership in a conjugate closed subgroup

`Langlands.NYLL.ClassFormation.conjugateClosedSubgroup_mem` proves the published
proposition `Langlands.NYLL.ClassFormation.conjugateClosedSubgroup_memStatement` of
module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`.

## Statement

The parameters are, in order, implicit `G : Type u_1`, instances `[Group G]`,
`[TopologicalSpace G]` and `[ContinuousMul G]`, and explicit
`K : ClosedSubgroup G` and `σ x : G`. The type of the theorem is exactly
`conjugateClosedSubgroup_memStatement K σ x`, which unfolds to

```lean
x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K
```

Here `conjugateClosedSubgroup K σ` (M026.001, module
`...Degree.NormLaws.Definitions`) is the closed subgroup whose underlying subgroup is
the pointwise conjugate `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
`σ⁻¹ K σ`. The theorem says `x ∈ σ⁻¹ K σ` exactly when `σ x σ⁻¹ ∈ K`.

## Implemented proof

The proof is the unchanged source tactic script.

1. `change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
   σ * x * σ⁻¹ ∈ K.toSubgroup` unfolds the Prop-valued target, the definition of
   `conjugateClosedSubgroup` and membership in a `ClosedSubgroup` to membership in
   the underlying subgroups. The `change` therefore also performs the unfolding of
   the opaque `...Statement` definition; no separate `show` is needed.
2. Mathlib's `Subgroup.mem_pointwise_smul_iff_inv_smul_mem` rewrites
   `x ∈ a • S` to `a⁻¹ • x ∈ S`, here with `a = ConjAct.toConjAct σ⁻¹`.
3. `simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]` turns
   `(ConjAct.toConjAct σ⁻¹)⁻¹ • x` into `ConjAct.toConjAct σ • x` and then into
   `σ * x * σ⁻¹`, closing the goal.

The only direct import is `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`, which transitively supplies
`conjugateClosedSubgroup` and Mathlib's pointwise subgroup actions and `ConjAct`.
The module opens the scoped `Pointwise` notation for the `•` in the `change`. The
kernel axioms reported by inspection are `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`, retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Unit M026.002 is the theorem `ClassFormation.conjugateClosedSubgroup_mem`:
docstring lines 47–49, `@[simp]` attribute line 50, statement lines 51–54 and
proof lines 55–58. Worker 5014 extracts it into this focused module, prefixes the
namespace with `Langlands.NYLL`, replaces the source imports by the published
statement module, and writes the conclusion as the published target applied to
the parameters. The source `@[simp]` attribute is omitted: the theorem's type is
now the Prop-valued target rather than a syntactic `↔`, and the statement module
records that the simp attributes are not part of the port. The docstring, the
parameter telescope and the proof script are the source ones. The source's section
variables (the theorem binds its own `G`), `noncomputable section` and its other
`open` lines are not used and are omitted.

This is an abstract subgroup-level fact of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
