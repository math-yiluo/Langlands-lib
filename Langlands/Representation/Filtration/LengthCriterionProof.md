# Bounded chains and actual composition length: proof

Author: Worker 244.

`Langlands.objectCompositionLengthCriterion` proves exactly
`ObjectCompositionLengthCriterion.{uK, uG, uV}` from
`Langlands.Representation.Filtration.LengthCriterionStatement`. The field,
monoid, and carrier universes remain independent. For every field `k`, monoid
`G`, representation `A : Rep.{uV} k G`, and bound `b : ℕ`, the theorem proves both
clauses:

1. `HasCompositionLengthAtMost A b` holds exactly when `m ≤ b` for every natural
   number `m` and every strictly increasing
   `c : Fin (m + 1) → Subrepresentation A.ρ`.
2. `HasCompositionLengthAtMost A b` implies
   `IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule`.

There are no further hypotheses: no finite-dimensionality, finite length,
nontriviality, or group structure. The imported definitions
`ObjectRepFiltration`, `HasCompositionSeriesLength`, and
`HasCompositionLengthAtMost` are reused unchanged, and so are the statement pair
and every pair it imports. All helpers below are in the namespace
`Langlands.LengthCriterionProof`.

## Actual quotients and covering steps

Let `S` and `T` be invariant subspaces of `ρ`. `lower S T` pulls `S` back to the
carrier of `T`, and `lower_le_comap` shows that it is stable under the action
on `T`. `quotientRep S T` is the actual quotient representation
`T.toRepresentation.quotient (lower S T) _` of `T` by `S`. Suppose `S` and `T`
are consecutive steps `s.subrepresentation i.castSucc` and
`s.subrepresentation i.succ` of an `ObjectRepFiltration`. Then this action is
definitionally `(s.gradedRepresentation i).ρ`. The proof compares invariant
subspaces through lattices only. It never constructs a linear equivalence
between this quotient and a quotient module over the monoid algebra.

`push S T X` is the image in the quotient of `X` pulled back to `T`.
`pull S T U` is the preimage in `T` of an invariant subspace `U` of the quotient,
viewed as an invariant subspace of `ρ`. Both are invariant by `quotientRep_mk`.
The small lemmas `mem_bot_iff`, `mem_top`, and `mkQ_mem_bot_iff` describe
membership in the bottom and top subrepresentations. In particular, the class of
`x ∈ T` is zero exactly when `x ∈ S`.

For `S ≤ T`, `isIrreducible_quotientRep_iff` proves that the quotient is
irreducible exactly when `S ⋖ T`. Mathlib's `Representation.IsIrreducible`
means `IsSimpleOrder` on the lattice of invariant subspaces, so it includes
nonzeroness.

- Suppose the quotient is irreducible. If `S = T`, every class is zero, so
  bottom equals top, which is impossible; hence `S < T`. Now suppose
  `S < X < T`. Then `push S T X` is either bottom or top. If it is bottom, every
  vector of `X` has zero class, so `X ≤ S`. If it is top, each `v ∈ T` has the
  class of some `y` in `X ∩ T`. Then `y - v ∈ S ≤ X`, so `v ∈ X`, and hence
  `T ≤ X`. Both cases contradict the choice of `X`.
- Conversely, suppose `S ⋖ T`. A vector of `T` outside `S` has nonzero class, so
  bottom differs from top in the quotient. Every invariant subspace `U` of the
  quotient satisfies `S ≤ pull S T U ≤ T`. By the covering relation,
  `pull S T U` equals `S` or `T`. If it equals `S`, every class in `U` has a
  representative in `S`, so `U` is bottom. If it equals `T`, every class lies
  in `U`, so `U` is top.

`hasSimpleFactors_iff_covBy` applies this to every step. A filtration
`s : ObjectRepFiltration A n` has simple factors exactly when
`s.subrepresentation i.castSucc ⋖ s.subrepresentation i.succ` for every
`i : Fin n`.

## Transfer to the monoid-algebra module

Let `e` be `Subrepresentation.subrepresentationSubmoduleOrderIso`, the order
isomorphism from the invariant subspaces of `A.ρ` to
`Submodule (MonoidAlgebra k G) A.ρ.asModule`. It preserves bottom, top, and
strict monotonicity. By `apply_covBy_apply_iff`, it preserves covering relations
in both directions. Combined with the covering-step characterization above,
this compares the two kinds of composition series.

- `exists_compositionSeries` sends an actual composition series of length `n`
  through `e`. The result is a Mathlib `CompositionSeries` of submodules of
  length `n`, with head `⊥` and last `⊤`.
- `hasCompositionSeriesLength_of_compositionSeries` reverses the comparison.
  It pulls back a `CompositionSeries` `s` with head `⊥` and last `⊤` through
  `e.symm`, then assembles the result with
  `ObjectRepFiltration.ofSubrepresentations`. This gives an actual composition
  series of length `s.length`.

Lengths are module lengths over `MonoidAlgebra k G`. Mathlib's `Module.length`
is the Krull dimension of the submodule lattice (`Module.coe_length`), not the
dimension of the underlying vector space.

## The two clauses

The forward direction of clause 1 is `le_of_hasCompositionSeriesLength`. Let
`c : Fin (m + 1) → Subrepresentation A.ρ` be strictly increasing, with arbitrary
endpoints. Its image under `e` is an `LTSeries` of length `m`. By
`Order.LTSeries.length_le_krullDim`, `m` is at most the Krull dimension of the
submodule lattice, that is, `Module.length`. Apply
`Module.length_compositionSeries` to the module composition series built from
an actual composition series of length `n ≤ b`; it shows that `n` equals
`Module.length`. Hence `m ≤ n ≤ b`.

The reverse direction is `hasCompositionLengthAtMost_of_bound`. Assume the
chain bound. Every `LTSeries` in the submodule lattice pulls back through
`e.symm` to a strictly increasing chain of invariant subspaces, so its length
is at most `b`. Since the Krull dimension is the supremum of these lengths, it
is at most `b`. In particular `Module.length ≠ ⊤`, so `Module.length_ne_top_iff`
gives finite length. Then `isFiniteLength_iff_exists_compositionSeries`
supplies a module composition series `s` from `⊥` to `⊤`. Its pullback is a
strictly increasing chain, so the bound gives `s.length ≤ b`, and
`hasCompositionSeriesLength_of_compositionSeries` makes it an actual
composition series. The proof uses Mathlib's module-length theory; it does not
build a maximal-length chain by hand.

Clause 2 is `isFiniteLength_of_hasCompositionSeriesLength`. The module
composition series from `exists_compositionSeries` runs from `⊥` to `⊤`, so
`isFiniteLength_of_exists_compositionSeries` gives finite length.

The zero bound and the zero representation need no separate case. Every step
above applies unchanged when `b = 0` and when `A` is the zero representation,
and no nontriviality is assumed anywhere.

## Provenance and scope

This is an internal algebraic bridge between the Library's actual
representation filtrations and Mathlib's length theory for modules over the
monoid algebra. Worker 122 authored the imported statement pair from Worker
170's specification. The proof uses only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorry` and no assumed criterion.

## Source motivation

The motivation is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977): the proof of Theorem 2.8, §2.14(2), on
printed page 449 / PDF page 10. Source ID: `bernstein-zelevinsky-1977-induced-i`;
original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

There the authors define `l'(τ) = Σ_{L ~ M} l(r_{L,G}(τ))`, a sum of lengths
of Jacquet modules. Exactness of the Jacquet functors makes `l'` additive, and
step (1) makes it positive on every nonzero subquotient of `π`. They conclude
that `l(π₀) ≤ l'(π₀)` for such subquotients, and in particular `l(π) ≤ l'(π)`.
The present criterion isolates one algebraic step of such an argument: it
turns a uniform bound on strict chains of invariant subspaces into an actual
composition series of bounded length and into finite module length. This
module does not derive any chain bound.

The general field-and-monoid theorem is not a verbatim statement of BZ77. It
constructs no Jacquet-module measure, involves no p-adic group, and does not
prove BZ77 Theorem 2.8. The cuspidal-induction application is separate work.
