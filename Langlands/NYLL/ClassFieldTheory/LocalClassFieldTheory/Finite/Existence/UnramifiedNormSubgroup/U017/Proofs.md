# NYLL M266.017: proof that trivial unramified norm classes are subgroup members

The paired Lean file proves the published target
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass_eq_one_iff_memStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.QuotientStatements`)
as the theorem
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass_eq_one_iff_mem`.

## Statement proved

The theorem's type is exactly the closed proposition
`unramifiedNormClass_eq_one_iff_memStatement.{u}`, with the target's single
universe parameter `u`. That proposition says: for every `K : Type u` with
instances `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, every `n : Nat` and every unit `x : Kˣ`,

`unramifiedNormClass K n x = 1 ↔ x ∈ unramifiedNormSubgroup K n`.

Here `unramifiedNormClass K n` is the published canonical projection
`Kˣ →* Kˣ ⧸ unramifiedNormSubgroup K n` (M266.013), defined as
`QuotientGroup.mk' (unramifiedNormSubgroup K n)`. The subgroup
`unramifiedNormSubgroup K n` (M266.011) consists of the units whose published
normalized valuation is divisible by `n` in `ℤ`. The degree `n` is
unrestricted; `n = 0` is included. The theorem adds no hypotheses.

## Implemented proof

1. `intro K _ _ _ _ n x` introduces the field, its four instances, the degree
   and the unit, in the target's order.
2. `exact QuotientGroup.eq_one_iff (N := unramifiedNormSubgroup K n) x`
   closes the goal. Mathlib's lemma states `(x : G ⧸ N) = 1 ↔ x ∈ N` for a
   normal subgroup `N`. The left side of the goal,
   `unramifiedNormClass K n x`, unfolds by definition to
   `QuotientGroup.mk' (unramifiedNormSubgroup K n) x`, which is
   definitionally the coercion `(x : Kˣ ⧸ unramifiedNormSubgroup K n)`, so
   `exact` accepts the lemma without a rewrite. The normality instance is
   found by instance search because `Kˣ` is commutative; it is the same
   search that elaborated the quotient in the published M266.013 definition.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry`, `admit`, native decision or new axiom.

## Original correspondence

The source is Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
That file's SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, with
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relevant unit is M266.017, theorem
`LocalClassFieldTheory.unramifiedNormClass_eq_one_iff_mem`, at lines 179–183:
the docstring at line 178, the signature at lines 179–182 and the proof at
line 183.

The source proof is
`rw [unramifiedNormClass_eq_one_iff, mem_unramifiedNormSubgroup_iff]`. It
rewrites with M266.016 (`unramifiedNormClass_eq_one_iff`, lines 169–176, whose
own proof is `QuotientGroup.eq_one_iff` composed with M266.012) and M266.012
(`mem_unramifiedNormSubgroup_iff`, lines 143–147, proved by `Iff.rfl`). After
both rewrites the two sides agree and `rw` closes the goal by reflexivity.

Worker 152 made these changes:

- The namespace gets the prefix `Langlands.NYLL`. The theorem's type is the
  published closed `…Statement` proposition rather than the source's explicit
  signature, so the proof first introduces the seven binders that the source
  had as parameters.
- The source's two rewrites are replaced by a direct application of Mathlib's
  `QuotientGroup.eq_one_iff`. The two routes reach the same equivalence: the
  source goes from the trivial class to valuation divisibility (M266.016) and
  back to subgroup membership (M266.012), and the direct route skips the
  divisibility detour. Neither M266.016 nor M266.012 is published as a proved
  theorem in the Library, so this replacement avoids a proof dependency on
  them.
- Only the published `QuotientStatements` module is imported. The source's
  `noncomputable section` and all other declarations of the source file are
  omitted.

## Actual dependencies

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.QuotientStatements`
  provides the target proposition. It imports
  `UnramifiedNormSubgroup.U013.Definitions`, which provides
  `unramifiedNormClass` and imports `U011.Definitions` (providing
  `unramifiedNormSubgroup`) and Mathlib's
  `Mathlib.GroupTheory.QuotientGroup.Defs`.
- From Mathlib: `QuotientGroup.eq_one_iff`.

The proof was compiled in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
with zero errors and zero warnings. Inspection of the theorem reported kind
`theorem`, level parameter `u`, and the three axioms listed above.

## Scope

This unit proves only that the kernel of the canonical quotient projection is
characterized elementwise by membership in the published subgroup. It does not
prove M266.014–.016. It asserts no identification of the subgroup with the
norm group of an unramified extension, and no reciprocity or existence result.

## Attribution

The Lean file keeps the original copyright, Apache-2.0 release and author
header for Naganori Yamaguchi (assisted by OpenAI Codex), and adds a dated
modification note. The retained license files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
