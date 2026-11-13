# The cardinal index of a subgroup in itself

This module proves the theorem
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_self`. For every
subgroup `K`, its type is the already published proposition
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_selfStatement K`,
applied to the theorem's own parameter `K`. This is the proof phase of
M006.013 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m006).

## Target and binders

The theorem's complete telescope and conclusion are

```lean
theorem relativeIndexCardinal_self {G : Type u} [Group G] (K : Subgroup G) :
    relativeIndexCardinal_selfStatement K
```

| Binder | Kind | Meaning |
| --- | --- | --- |
| `G : Type u` | implicit | The ambient group's carrier, in an arbitrary universe `u` |
| `[Group G]` | instance-implicit | Its group structure |
| `K : Subgroup G` | explicit | An arbitrary subgroup |

These are the published statement's parameters in the same order and
binder kinds; `G` and `[Group G]` come from the module's `variable`
line. The published statement unfolds to

```lean
relativeIndexCardinal (le_refl K) = 1
```

in `Cardinal.{u}`. Through the published data module U010 Definitions,
`relativeIndexCardinal (le_refl K)` is
`intersectionIndexCardinal K K`, which is
`Cardinal.mk (K ⧸ K.subgroupOf K)`: the cardinality of the actual type
of left cosets of `K.subgroupOf K` in `K`. The theorem has no
finiteness, normality or other hypothesis. It holds for every group and
every subgroup, including when `G` or `K` is infinite.

The sole direct import is the published module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements`,
which supplies the target and, through its imports, the U010 data and
the Mathlib group-quotient and cardinal API used below.

## Implemented proof

The proof is the original tactic proof at source lines 154–164, unchanged:

```lean
let α := K ⧸ K.subgroupOf K
let : Subsingleton α := by
  constructor
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y
  apply Quotient.eq''.mpr
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  exact (x⁻¹ * y).2
change Cardinal.mk α = 1
exact Cardinal.mk_eq_one α
```

1. It names the coset type `α := K ⧸ K.subgroupOf K` and builds a
   local, unnamed `Subsingleton α` instance. Given two classes `q` and
   `r`, core Lean's `Quotient.inductionOn₂` reduces to classes of
   representatives `x y : K`. Mathlib's `Quotient.eq''`
   (`Mathlib/Data/Quot.lean`, line 735) turns equality of the classes into
   the left-coset relation for `K.subgroupOf K`.
   `QuotientGroup.leftRel_apply` (`Mathlib/GroupTheory/Coset/Defs.lean`,
   line 71) rewrites it as `x⁻¹ * y ∈ K.subgroupOf K`, and
   `Subgroup.mem_subgroupOf` (`Mathlib/Algebra/Group/Subgroup/Map.lean`,
   line 315) as `((x⁻¹ * y : K) : G) ∈ K`. The membership proof
   `(x⁻¹ * y).2` of the element `x⁻¹ * y` of `K` closes this.
2. `change Cardinal.mk α = 1` replaces the published statement by its
   definitional unfolding through `relativeIndexCardinal_selfStatement`,
   `relativeIndexCardinal` and `intersectionIndexCardinal`.
3. Mathlib's `Cardinal.mk_eq_one (α : Type u) [Subsingleton α]
   [Nonempty α] : #α = 1` (`Mathlib/SetTheory/Cardinal/Defs.lean`,
   line 248) concludes. Its `Subsingleton` argument is the local
   instance of step 1. Its `Nonempty` argument is found by instance
   synthesis: a development probe showed that for
   `K ⧸ K.subgroupOf K` it is core `instNonemptyOfInhabited` applied to
   Mathlib's `Inhabited` instance on subgroup quotients
   (`Mathlib/GroupTheory/Coset/Defs.lean`, lines 193–195), whose default
   element is the class of `1`.

The helper instance is a `let` inside the proof and does not escape it.
No global instance, auxiliary declaration or choice of coset
representatives is introduced. The same probe checked by `rfl` that
`relativeIndexCardinal_selfStatement K` is definitionally
`Cardinal.mk (K ⧸ K.subgroupOf K) = 1`.

Mathlib's `Subgroup.subgroupOf_self` and
`QuotientGroup.subsingleton_quotient_top` suggest an alternative route;
it is not used here, because the original proof already compiles in the
approved environment.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`,
lines 151–164](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean#L151-L164):
the docstring at line 151, the `@[simp]` theorem with its signature at
152–153 (ending in `:= by`) and the tactic proof at 154–164. The data it uses are at lines
131–141. The complete pinned original file was read and its SHA-256
verified as
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.

| Original declaration | Adapted declaration in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| `ClassFormation.relativeIndexCardinal_self` (theorem, `@[simp]`) | `relativeIndexCardinal_self` (theorem), proving the published target |
| Same theorem's statement | Existing `relativeIndexCardinal_selfStatement` |
| `ClassFormation.relativeIndexCardinal` | Existing `relativeIndexCardinal` |
| `ClassFormation.intersectionIndexCardinal` | Existing `intersectionIndexCardinal` |

Only the first row introduces a declaration here. Modifications by
Worker 173 on 13 November 2026 are: add the `Langlands.NYLL` namespace
prefix; replace the source import by the sole U012 Statements import;
give the theorem the type `relativeIndexCardinal_selfStatement K` in place
of the literal equation it unfolds to; omit the `@[simp]` attribute, the
source section's universe `v`, `D : Type v` and `[Group D]`, which do
not occur in this declaration, and all other source declarations. The
theorem name, its docstring, its binders and the proof steps are kept.
With the statement constant as its type, the theorem is not a
syntactic equation, so the omitted `@[simp]` attribute is not restored.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Searches of the
workspace, current Library, staging and shared drafts found no earlier
proof of this target.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The original proof needed no change there. A development check compiled
the module with no diagnostics. It found a theorem with level parameter
`u` using only the axioms `propext`, `Classical.choice` and `Quot.sound`.
This check is not independent semantic acceptance or Integrator
publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 173 adapted this proof directly from
the pinned original and wrote this companion. Worker 120's statement and
the imported data are used unchanged; all imported Library modules and
their paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are byte-identical to the
retained originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This proof concerns only the cardinal index of a subgroup in itself. It
proves neither M006.012 nor M006.014, nor any image–kernel index law,
local reciprocity or host class-formation theorem.
