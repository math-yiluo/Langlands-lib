# Reduced-translation exhaustion under surjective bialgebra maps

Authors: Worker 1450 (Lean proof and first Markdown draft); Worker 1411
(Markdown revision and submission).

This module proves `conilpotenceQuotient`, whose type is exactly
`ConilpotenceQuotientStatement.{u,v,w}` from
`Langlands.GroupScheme.CoalgebraUnipotence.Statements`, for independent
universe parameters `u`, `v` and `w`:

```
∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B]
  (C : Type w) [Ring C] [Bialgebra k C] (q : B →ₐc[k] C),
  Function.Surjective q → IsLocallyConilpotent k B → IsLocallyConilpotent k C
```

That is, if a surjective bialgebra homomorphism `q : B →ₐc[k] C` is given and
every element of `B` lies in some reduced-translation level
`reducedLevel k B n`, then every element of `C` lies in some
`reducedLevel k C n`. The module imports the published `Statements` module and
uses `reducedLevel`, `IsLocallyConilpotent` and
`AffineLinearEmbedding.rightAct` unchanged.

## Elementary lemmas on the levels

Throughout, `k` is a field and `B`, `C` are `k`-bialgebras (`[Ring B]`,
`[Bialgebra k B]`), in arbitrary universes.

- `mem_reducedLevel_zero` (a `simp` lemma): `b ∈ reducedLevel k B 0 ↔ b = 0`,
  since level `0` is `⊥`.
- `mem_reducedLevel_succ`: `b ∈ reducedLevel k B (n + 1)` if and only if
  `rightAct f b ∈ reducedLevel k B n` for every `f : Module.Dual k B` with
  `f 1 = 0`. Both lemmas are proved by `simp` after unfolding
  `reducedLevel`; the second also uses `Submodule.mem_iInf` and
  `Submodule.mem_comap` to turn the infimum over the subtype of functionals
  vanishing at `1` into the stated quantifier.
- `reducedLevel_le_succ` and `reducedLevel_mono`: the levels increase,
  `reducedLevel k B n ≤ reducedLevel k B (n + 1)`, proved by induction on `n`
  (level `0 = ⊥` is below everything; the inductive step applies the induction
  hypothesis to each `rightAct f b`), and hence form a monotone sequence by
  `monotone_nat_of_le_succ`. These lemmas are not needed for the quotient
  theorem; they are kept in this module for the matrix criterion proof that
  follows it.

## Naturality of right translation

`map_rightAct q f b` states, for a bialgebra homomorphism `q : B →ₐc[k] C`, a
functional `f : Module.Dual k C` and `b : B`,

```
q (rightAct (f ∘ₗ (q : B →ₗ[k] C)) b) = rightAct f (q b).
```

Writing `comul b = ∑ b₁ ⊗ b₂`, the left side is
`q (∑ f (q b₂) • b₁) = ∑ f (q b₂) • q b₁`. The right side is computed from
`comul (q b) = (q ⊗ q) (comul b)` (Mathlib's
`CoalgHomClass.map_comp_comul_apply`), so it is the same sum. In Lean, after
unfolding `rightAct_apply`, the identity is proved for an arbitrary tensor
`t : B ⊗[k] B` in place of `comul b`, by `TensorProduct.inductionOn`: the pure
tensor case is a `simp` computation and the sum case follows from additivity.

## Images of levels

`map_mem_reducedLevel q n hb` states that `b ∈ reducedLevel k B n` implies
`q b ∈ reducedLevel k C n`. The proof is by induction on `n`, generalizing
`b`.

- For `n = 0`, `b = 0`, so `q b = 0`.
- For `n + 1`, let `f : Module.Dual k C` with `f 1 = 0`. The pulled-back
  functional `f ∘ₗ q` also vanishes at `1`, because `q 1 = 1`. By the
  hypothesis on `b`, `rightAct (f ∘ₗ q) b ∈ reducedLevel k B n`, so by the
  induction hypothesis its image under `q` is in `reducedLevel k C n`. By
  `map_rightAct`, this image is `rightAct f (q b)`, which is what
  `mem_reducedLevel_succ` requires.

Only the compatibility of `q` with comultiplication and its preservation of
`1` are used; surjectivity is not needed for this lemma.

## The quotient theorem

`isLocallyConilpotent_of_surjective q hq hB` proves
`IsLocallyConilpotent k C`: given `c : C`, surjectivity gives `b` with
`q b = c`, the hypothesis on `B` gives `n` with `b ∈ reducedLevel k B n`, and
`map_mem_reducedLevel` gives `c ∈ reducedLevel k C n` with the same `n`.
`conilpotenceQuotient` introduces the binders of
`ConilpotenceQuotientStatement.{u,v,w}` and applies this lemma.

## Provenance

These are internal consequences of the definitions in
`CoalgebraUnipotence.Definitions`; no literature assertion is assumed. The
statement is the analogue, for the reduced-translation filtration, of the
remark in the proof of Milne's Theorem 14.5 that quotients of coconnected Hopf
algebras are coconnected; `Statements.md` records that motivation. The Lean
proof above is self-contained and does not follow Milne's argument about
coconnected filtrations.
