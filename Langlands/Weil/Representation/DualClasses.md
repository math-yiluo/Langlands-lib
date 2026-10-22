# Double duals and the dual involution on continuous irreducible classes

Worker 17 authored this internal construction at Worker 24's request; it
supplies the dual counterpart of the published `TwistClasses` interface and
follows its naming. It introduces no new model of representations or
classes: it works with the published full algebraic dual `dual`, its class
map `dualClass`, the genuine-class quotients `IsomorphismClasses`,
`IsomorphismClassesWith` and `ContinuousIrreducibleClasses`, and the
published operation-closure proofs.

## Algebraic part

The algebraic part works over an arbitrary field, with independent
coefficient, group and carrier universes.

- `dualDualEquiv A : Equiv A (dual (dual A))` is a genuine equivalence of
  representations. Its linear part is Mathlib's evaluation isomorphism
  `Module.evalEquiv K A` onto the double dual, `v ↦ (ℓ ↦ ℓ v)`, which is an
  isomorphism because the carrier is finite-dimensional. Its intertwining
  property is the one of the published `Langlands.bidualIntertwining`.
- `rank_dual` states `(dual A).rank = A.rank`, from Mathlib's
  `Subspace.dual_finrank_eq`.
- `dualClass_classOf` states that `dualClass` sends the class of `A` to the
  class of `dual A`; `classRank_dualClass` states that it preserves rank.

## Complex coefficients

For complex coefficients the carrier universe of the dual, `max 0 uV`, is
`uV`, so `dualClass` is an endomap of `IsomorphismClasses ℂ G`.

- `dualClass_dualClass`: applying `dualClass` twice returns the class, by the
  inverse of `dualDualEquiv`. `dualClass_involutive` restates this, and
  `dualClassEquiv` packages `dualClass` as a permutation that is its own
  inverse (`dualClassEquiv_apply`, `dualClassEquiv_symm`).
- `isIrreducible_dual_iff` is the published
  `Weil.OperationClosure.irreducible_dual_iff`, read on objects; it needs no
  topology.
- For a topological group `G`, `isContinuous_dual_iff` is the published
  `Weil.OperationClosure.continuous_dual_iff`, in the usual complex topology
  on endomorphisms. Continuity of inversion on `G` is used there, so this part
  assumes `IsTopologicalGroup G`, unlike the twist interface.

## Continuous irreducible classes

- `continuousIrreducibleDual` sends an object carrying proofs of continuity and
  irreducibility to its dual with the transported proofs.
- `continuousIrreducibleDualClass` descends it through the existing property
  quotient `IsomorphismClassesWith (IsContinuous ∧ IsIrreducible)`, using the
  published `dualEquiv` on genuine equivalences.
  `forget_continuousIrreducibleDualClass` states that forgetting the
  conditions turns it into `dualClass`, and
  `continuousIrreducibleDualClass_continuousIrreducibleDualClass` that it is an
  involution, again by `dualDualEquiv`.
- `continuousIrreducibleDualEquiv n` restricts this to the existing
  `ContinuousIrreducibleClasses G n`. The rank certificate follows from the
  forgetful formula and `classRank_dualClass`. Both directions are the same
  map, so `continuousIrreducibleDualEquiv_symm` holds by definition.
  The representative formula `continuousIrreducibleDualEquiv_mk` (the class of
  `⟨A, h⟩` goes to the class of `dual A` with the transported proofs), the
  forgetful square `forget_continuousIrreducibleDualEquiv`, and the involution
  laws `continuousIrreducibleDualEquiv_apply_apply` and
  `continuousIrreducibleDualEquiv_trans_self` are provided.

Every natural rank is allowed, including zero as in the existing class
definition. Group and carrier universes are independent. No Weil-Deligne,
open-inertia or Frobenius-semisimple dual class map is included; preservation
of those conditions under duality is not asserted here.

## Provenance

This is a derived construction. The dual itself is the published algebraic
dual of `Langlands.Weil.Representation.Dual`, whose Markdown records its
source (the inverse-element action on the full algebraic dual). Isomorphism
classes of finite-dimensional representations are the sets `M(G)` of Tate,
*Number theoretic background*, in *Automorphic Forms, Representations and
L-Functions* (Corvallis, 1979), Part II, §2, printed page 9 (literature ID
`tate-1979-number-theoretic-background`, PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`).
The double-dual identification is standard finite-dimensional linear algebra,
taken from Mathlib; continuity and irreducibility of the dual are the
published operation-closure proofs. No further literature claim is
translated.

Project imports, all published in Library
`3b5205fa6ae98b1b2f57b8bfc33e99d78771f240`:
`Langlands.Weil.Representation.Dual`,
`Langlands.Weil.Representation.Predicates`, and
`Langlands.Weil.Representation.OperationClosureProof`.
The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
