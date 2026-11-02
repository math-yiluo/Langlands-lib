# The Coxeter double-coset minimum length criterion

`Langlands.Group.RelativeWeylIndexing.minimalityLengthCriterion_proof` proves
the exact published proposition `minimalityLengthCriterion cs` from
`Langlands.Group.RelativeWeylIndexingTargets`.

For every `B : Type u`, `W : Type v`, `[Group W]`, Coxeter matrix `M` on `B`,
and `cs : CoxeterSystem M W`, it states that, for all `I J : Finset B` and
`w : W`, least length in the entire double coset `W_I w W_J` is equivalent to
strict length increase under each left simple reflection in `I` and each
right simple reflection in `J`. The proof uses exactly the published
`standardSubgroup`, `doubleCoset`, and `IsMinimal` constructions. It preserves
independent universes, infinite ambient systems, empty subsets, and empty
simple-index types.

## Provenance and scope

The statement's original-source provenance is recorded in the unchanged
`RelativeWeylIndexingTargets.md` and `RelativeWeylIndexing.md`: the intrinsic
Coxeter comparison underlies Renard V.4.6(i), printed pp.120–121, and the
minimal-representative indexing used by Aubert 1995, printed pp.2180–2183.
The implemented proof below is an internal Coxeter argument. It makes no
claim to implement Carter's proof or to identify actual relative roots or
Levi subgroups.

All needed exchange facts are proved in the companion
`Langlands.Group.RelativeWeylExchange`, whose Markdown explains the signed
action and its dependencies. No root realization, exchange hypothesis,
uniqueness theorem, intersection theorem, or finiteness hypothesis is an
input to the result. No other relative-Weyl target is used as a premise.

## One-sided length additivity

The public helpers `wordProd_mem_standard` and `exists_standard_word`
relate words on `I` to membership in `W_I`, and are shared with the
[uniqueness proof](RelativeWeylMinimalUniqueProof.md).
Subgroup closure induction proves that every element of `W_I` has a word
whose letters lie in `I`: generators are singleton words, multiplication is
concatenation, and inversion is word reversal. Taking the least natural
number among the lengths of such words supplies a shortest `I`-word for
each element. This minimization needs no finiteness of the ambient group or
of the set of words.

The main internal lemma, `shortest_word_length_add`, takes a left-coset
minimum `v` and a shortest `I`-word `α`. It proves

\[
\ell((\pi\alpha)v)=|\alpha|+\ell(v).
\]

The proof inducts on `α`. For `α = i :: α'`, the tail is shortest for its
own product, so the induction hypothesis applies. Multiplication by `s_i`
either adds one to the length or subtracts one. In the decreasing case,
choose a reduced word `η` for `v` and apply exchange to `α' ++ η`.

* If the erased letter lies in `α'`, cancellation of `v` gives a shorter
  `I`-word for `π α`, contradicting the choice of `α`.
* If it lies in `η`, the shortened word represents
  `(π α')⁻¹ s_i (π α') v`. Its left factor belongs to `W_I`, while its
  length is at most `|η|-1 < ℓ(v)`. This contradicts left-coset minimality.

The decreasing case is impossible. Applying this word formula also with
`v=1` identifies the shortest `I`-word length with ambient Coxeter length.
The public helper `length_mul_of_left_minimal` therefore gives

\[
\ell(av)=\ell(a)+\ell(v),\qquad a\in W_I,
\]

for a left-coset minimum `v`. `length_mul_of_right_minimal` proves the right
version by inversion and `cs.length_inv`.

## Simple conditions and one-sided minima

`exists_minimal_in_doubleCoset_unrestricted` chooses the least natural
number attained by length in a nonempty double coset. The published
`mul_mem_doubleCoset` shows that this chosen element satisfies `IsMinimal`.
This strengthens the available finite-group existence result for use here;
it assumes no finiteness.

For `left_minimal_of_simple`, choose a minimum `v` in `W_I w` using the
preceding existence result with `J=∅`. Express `w=(π α)v` with `α` a shortest
`I`-word. If `α=i::α'` were nonempty, additivity would give
`ℓ(w)=|α'|+1+ℓ(v)`, while cancellation of the initial `s_i` and the ordinary
word-length bound would give `ℓ(s_i w)≤|α'|+ℓ(v)`. This contradicts the
assumed strict increase at every `i∈I`. Hence `α` is empty, `w=v`, and `w`
is a left-coset minimum. `right_minimal_of_simple` applies the same argument
to `w⁻¹`.

## The double-coset equivalence

The forward implication tests `IsMinimal` on each simple reflection and
the identity on the opposite side. The resulting weak inequalities are
strict because Mathlib proves that simple multiplication never preserves
Coxeter length.

For the reverse implication, the preceding helpers make `w` both a left-
and a right-coset minimum. Choose a minimum `v` in its whole double coset
and write

\[
v=a w b,\qquad a\in W_I,\quad b\in W_J.
\]

Both `v` and `w` have the relevant one-sided minimality. Length additivity
at `w` and at `v` gives

\[
\begin{aligned}
\ell(a)+\ell(w)&=\ell(a w)=\ell(v b^{-1})=\ell(v)+\ell(b),\\
\ell(w)+\ell(b)&=\ell(w b)=\ell(a^{-1}v)=\ell(a)+\ell(v).
\end{aligned}
\]

Adding and cancelling yields `ℓ(w)=ℓ(v)`. For arbitrary `x∈W_I` and
`y∈W_J`, apply minimality of `v` to

\[
(xa^{-1})v(b^{-1}y)=xwy.
\]

Replacing `ℓ(v)` by `ℓ(w)` proves the published `IsMinimal` predicate for
`w` and completes the equivalence.

The direct imports are the unchanged published target module and the
companion exchange module. Apart from those, the proof uses subgroup
closure and membership laws, word products and length bounds, natural-number
minimization, inversion, and elementary natural-number arithmetic. The
Coxeter prerequisites are derived within this contribution rather than
added to the target's assumptions.
