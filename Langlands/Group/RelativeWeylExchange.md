# Simple exchange from the Coxeter presentation

This is an internal prerequisite for
`Langlands.Group.RelativeWeylIndexing.minimalityLengthCriterion_proof`. It derives simple exchange from the
pinned Mathlib Coxeter presentation and inversion-sequence API. The proof is an
internal argument; it does not import an exchange axiom, a parabolic normal form,
or any of the Library's unproved relative-Weyl targets.

The parameters are `B : Type u`, `W : Type v`, a group structure on `W`, a
Coxeter matrix `M` on `B`, and `cs : CoxeterSystem M W`. The universes are
independent. Neither type needs to be finite or nonempty.

## Signed action and the Coxeter relations

Write `s_i = cs.simple i`, `π ω = cs.wordProd ω`, and
`L(ω) = cs.leftInvSeq ω`. For a function `f : W → ZMod 2`, define

\[
(A_i f)(t) = f(s_i t s_i) + [t=s_i].
\]

Here the bracket is one if its equality holds and zero otherwise. These are
functions in the endomorphism monoid of `W → ZMod 2`, with composition as
multiplication. Induction on a word proves the formula implemented by
`signedWord_apply`:

\[
(A_\omega f)(t)
 = f((\pi\omega)^{-1}t(\pi\omega))
   + \#\{\text{occurrences of }t\text{ in }L(\omega)\}\pmod 2.
\]

For `m = M i j`, the word `alternatingWord i j (2*m)` has product one. The
`k`th entry of its left inversion sequence is

\[
s_i(s_j s_i)^k,\qquad 0\le k<2m.
\]

The implementation obtains this formula from Mathlib's
`getElem_leftInvSeq_alternatingWord` and
`prod_alternatingWord_eq_mul_pow`. The Coxeter relation
`(s_j*s_i)^m = 1` identifies entry `m+k` with entry `k`. Thus the inversion
sequence is the concatenation of two identical lists. Every count vanishes in
`ZMod 2`, including when `m=0`, and the displayed action formula proves
`(A_i*A_j)^m = 1`.

`cs.lift` therefore gives a homomorphism `signedAction` from `W` to these
endomorphisms. Evaluating the action of equal word products on the zero
function proves `invCount_eq_of_prod_eq`: every individual inversion count has
the same parity for any two expressions for the same element.

## Exchange

For a simple left descent of `w = π ω`, take a reduced word `η` for `s_i*w`.
The simple descent length law shows that `i :: η` is a reduced word for `w`.
Its left inversion sequence starts with `s_i` and has no duplicates by
Mathlib's `IsReduced.nodup_leftInvSeq`. Its count of `s_i` is consequently one.
Parity invariance implies that `s_i` occurs in `L(ω)` as well. This is
`simple_mem_leftInvSeq_of_descent`.

`simple_left_exchange` chooses an index `k` of this occurrence and applies
Mathlib's `getD_leftInvSeq_mul_wordProd`. It proves

\[
s_i\,\pi\omega = \pi(\omega.\mathrm{eraseIdx}\ k),
\qquad k<\omega.\mathrm{length}.
\]

The input word need not be reduced. The final helper
`simple_left_exchange_append` locates the erased letter in the first or the
second part of a concatenation. That split is used by the one-sided length
additivity proof.

## Dependencies and provenance

The mathematical inputs are the pinned Mathlib modules
`Mathlib.GroupTheory.Coxeter.Inversion` and its `Length`/`Basic` imports. In
particular, the proof uses the universal presentation map `cs.lift`, the
Coxeter relations, existence of reduced words, simple descent length laws,
the explicit alternating inversion sequence, reduced inversion-sequence
no-duplicates, and the identity relating an inversion entry to erasure of its
letter. The additional imports `Mathlib.Data.List.Count` and
`Mathlib.Data.List.Nodup` supply list-count facts.

This module supplies an internal Coxeter prerequisite for the Library's
minimum criterion. Its proof route is independent of the original-literature
route recorded in `RelativeWeylIndexingTargets.md`; no direct reading or
implementation of Carter is claimed here.
