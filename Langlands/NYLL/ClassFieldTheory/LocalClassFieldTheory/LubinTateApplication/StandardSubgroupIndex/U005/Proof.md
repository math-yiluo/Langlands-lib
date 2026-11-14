# NYLL M377.005: exact proof of subgroup equality from equal nonzero indices

This module proves
`Langlands.NYLL.LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zero.{u}`.
Its type is exactly the existing Library proposition
`Langlands.NYLL.LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zeroStatement.{u}`:

```lean
∀ {G : Type u} [Group G] {H N : Subgroup G},
  H ≤ N → H.index = N.index → H.index ≠ 0 → H = N
```

The complete group and subgroup telescope is introduced from that proposition.
The theorem preserves arbitrary universe `u` and adds no hypotheses.
Neither the ambient group nor the subgroups are assumed finite, commutative
or normal. The nonzero-index hypothesis excludes Mathlib's infinite-index
convention `index = 0`.

## Implemented proof

The proof installs `H.FiniteIndex` locally using `H.index ≠ 0`. By
antisymmetry it suffices to show `N ≤ H`. If this fails, containment
`H ≤ N` implies `H ≠ N` and hence `H < N`. Mathlib's
`Subgroup.index_strictAnti` then gives `N.index < H.index`.
Rewriting by the supplied equality of indices produces
`N.index < N.index`, contradicting `Nat.lt_irrefl`.

The sole direct import is the unchanged published target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex.U005.Statements`,
whose sole Mathlib import is `Mathlib.GroupTheory.Index`. No local-field,
valuation or Lubin–Tate data is required. No helper declaration or global
instance is added.

## Source and modifications

The proof is adapted from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned at
`fbd320cd8b1b06487c58227e92eb135794267709`.
The source file is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean`,
with SHA-256
`09a3021fc016de44aa5717a06d80cfa849c2ec642f9301a93538f1bb184e42b8`.
The declaration is M377.005:
`LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zero`,
signature at lines 124–128 and proof at lines 129–139.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The source proof body is retained. Worker 580 prefixes the namespace by
`Langlands.NYLL`, replaces the explicit signature by the exact published
Prop-valued target, makes its universe `u` explicit, and introduces that
target's entire internal telescope. The unrelated source imports, enclosing
local-field variables, namespace openings and noncomputable section are
omitted. The published target pair and all its imports are unchanged.
These changes do not alter the three hypotheses or conclusion.

The source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The pinned source was read directly; no applicable NYLL erratum was found
in the Library's `notes/errata/`.

The original copyright, Apache-2.0 and author header is retained verbatim,
with a separate modification notice. The existing `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

## Development validation

The focused `lean_check` in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) successfully built this
module with zero errors and zero warnings. Inspection identified a theorem
with the single universe parameter `u` and only the standard assumptions
`propext`, `Classical.choice` and `Quot.sound`.
This development check is separate from exact-target submission validation
and independent semantic review.
