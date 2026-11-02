# Uniqueness of the longest minimal parabolic representative

`Langlands.Group.RelativeWeylIndexing.longestRepresentativeUnique_proof`
proves the exact published proposition `longestRepresentativeUnique cs`
from `Langlands.Group.RelativeWeylIndexingTargets`.

The parameters are `B : Type u`, `W : Type v`, `[Group W]`, `[Fintype W]`,
`M : CoxeterMatrix B`, and `cs : CoxeterSystem M W`, with independent
universes. For every `J : Finset B` and `w : W`, if `w ∈ minimalReps cs J ∅`
and `cs.length x ≤ cs.length w` for every `x ∈ minimalReps cs J ∅`, then
`w = longestRep cs J`. There is no `[Fintype B]` or nonemptiness assumption,
`J` may be empty, and no restriction on the Coxeter matrix is made.

## Provenance and dependencies

The original-source provenance of the target is recorded in the unchanged
`RelativeWeylIndexing.md` and `RelativeWeylIndexingTargets.md`: Aubert 1995,
printed pp.2180–2183, uses the longest member `w_J` of `D(J,∅)`. That
source does not prove uniqueness of the maximum. The argument here is an
internal Coxeter proof. No direct reading or implementation of Carter is
claimed.

The sole direct import is the published
`Langlands.Group.RelativeWeylMinimalityProof`. From it the final step uses
`length_mul_of_left_minimal` (length additivity at a left-coset minimum).
The published constructions `standardSubgroup`, `minimalReps`,
`mem_minimalReps`, `IsMinimal`, `longestRep`, `longestRep_mem` and
`length_le_longestRep` come from `RelativeWeylIndexing`. The published
minimum-criterion and minimum-uniqueness theorems are not used. No
longest-element, exchange, parabolic-decomposition or uniqueness premise is
added.

The signed-action machinery is reused from the published
`Langlands.Group.RelativeWeylExchange` (see its Markdown). Its unchanged
`signedSimple`, `signedWord` and `signedAction` definitions, together with
`signedWord_apply` and `signedAction_word`, are public so this module can
use them directly. The duplicate private definitions and proofs have been
removed; the reflection-parity construction retains the same action.

Mathlib inputs are the Coxeter presentation lift `CoxeterSystem.lift`,
word products and their surjectivity, left inversion sequences,
`isLeftInversion_of_mem_leftInvSeq`, reduced-word existence, the
alternating-word inversion formula, the reflection API
(`IsReflection`, `IsReflection.conj`, `IsReflection.mul_self`,
`IsReflection.length_mul_right_ne`), the simple-multiplication length
dichotomies, `exists_leftDescent_of_ne_one`, the length bound for products,
`length_inv`, `length_eq_zero_iff`, and `Finset.exists_max_image`.

## The reflection parity cocycle

Write `s_i = cs.simple i`, `π ω = cs.wordProd ω` and `L(ω) = cs.leftInvSeq ω`.
The endomorphisms

\[
(A_i f)(t) = f(s_i t s_i) + [t = s_i]
\]

of `W → ZMod 2` satisfy the Coxeter relations, since the left inversion
sequence of each defining alternating word consists of two identical
halves. Hence `cs.lift` gives a monoid homomorphism `signedAction` with
`signedAction (π ω) = A_ω`. By induction on words,

\[
(A_\omega f)(t) = f((\pi\omega)^{-1} t\, \pi\omega) + \#\{t \text{ in } L(\omega)\} \pmod 2.
\]

The public definition `reflectionParity cs w t` evaluates
`signedAction cs w` at the zero function and at `t`. Then:

* `reflectionParity_wordProd`: for every word `ω`,
  `reflectionParity cs (π ω) t` is the number of occurrences of `t` in
  `L(ω)` modulo two. In particular this parity does not depend on the word.
* `parityAction_apply` (private): every `w` is a word product, so
  `signedAction cs w f t = f(w⁻¹ t w) + reflectionParity cs w t`.
* `reflectionParity_mul`: since `signedAction` is multiplicative and
  composition is the monoid product,

  \[
  \eta(xy, t) = \eta(x, t) + \eta(y, x^{-1} t x),
  \]

  writing `η = reflectionParity cs`.
* `reflectionParity_one`: `η(1, t) = 0`, from the empty word.
* `reflectionParity_simple_self`: `η(s_i, s_i) = 1`, from the word `[i]`.

## Strong exchange for a reflection

`reflectionParity_self`: if `t = w s_i w⁻¹`, then `η(t, t) = 1`. The cocycle
law at `w · w⁻¹ = 1` gives `0 = η(w, t) + η(w⁻¹, s_i)`. Applying it to
`t = w · (s_i w⁻¹)` and then to `s_i · w⁻¹` gives

\[
\eta(t,t) = \eta(w,t) + \eta(s_i,s_i) + \eta(w^{-1}, s_i) = 1 .
\]

`length_mul_lt_of_reflectionParity`: if `η(w, t) = 1`, choose a reduced
word `ω` for `w`. The count of `t` in `L(ω)` is odd, so `t ∈ L(ω)`, and
Mathlib's `isLeftInversion_of_mem_leftInvSeq` gives `ℓ(t w) < ℓ(w)`.

`length_reflection_mul_lt_iff`: for a reflection `t`,
`ℓ(t w) < ℓ(w) ↔ η(w, t) = 1`. The reverse implication is the previous
lemma. Conversely, if `ℓ(t w) < ℓ(w)` but `η(w, t) = 0`, the cocycle law and
`t⁻¹ t t = t` give `η(t w, t) = η(t, t) + η(w, t) = 1`. The previous lemma
then gives `ℓ(w) = ℓ(t (t w)) < ℓ(t w)`, a contradiction. A value of
`ZMod 2` is `0` or `1` (private `zmod_two_cases`, by `decide`).

## Length complement at a longest element

`length_mul_add_length_of_forall_length_le`: let `w₀` satisfy
`ℓ(x) ≤ ℓ(w₀)` for all `x`. No finiteness of `W` is assumed in this lemma.
For every reflection `t`, maximality gives `ℓ(t w₀) ≤ ℓ(w₀)`, and Mathlib's
parity lemma `length_mul_right_ne` excludes equality. Hence
`η(w₀, t) = 1`. The lemma then proves

\[
\ell(x w_0) + \ell(x) = \ell(w_0)
\]

by induction on `ℓ(x)`. Length zero means `x = 1`. Otherwise choose a
left descent `s_i` of `x` and put `y = s_i x`, so `ℓ(y) = ℓ(x) − 1` and
`x = s_i y`. Since `s_i` is not a left descent of `y`, the previous
section forces `η(y, s_i) = 0`. The element `y⁻¹ s_i y` is a reflection, so
`η(w₀, y⁻¹ s_i y) = 1`. The cocycle law gives `η(y w₀, s_i) = 1`, hence
`ℓ(x w₀) = ℓ(s_i (y w₀)) = ℓ(y w₀) − 1`. The induction hypothesis for `y`
completes the step.

Three consequences are recorded:

* `exists_length_complement`: with `[Fintype W]`, a maximum of `cs.length`
  over `Finset.univ` satisfies the complement law.
* `eq_of_forall_length_le`: if `w₀` is longest and `ℓ(w₀) ≤ ℓ(y)`, then the
  complement law at `x = y w₀⁻¹` forces `ℓ(y w₀⁻¹) = 0`, so `y = w₀`.
* `eq_of_forall_length_mul_simple_lt`: if every simple reflection is a
  right descent of `c`, then `c = w₀`. Otherwise `c⁻¹ w₀ ≠ 1` has a left
  descent `s_i`, and `w₀ = (c s_i)(s_i c⁻¹ w₀)` would have length at most
  `ℓ(c) − 1 + ℓ(c⁻¹ w₀) − 1 = ℓ(w₀) − 2`, by the complement law at
  `x = c⁻¹`.

The last two are not used by the target proof. They are public helpers
for the related finite cancellation work.

## The longest member of `D(J,∅)`

The private `eq_inv_mul_of_longest_minimal` assumes `[Fintype W]`, a longest
element `w₀` of `W`, an element `a ∈ W_J = standardSubgroup cs J` of maximal
length in `W_J`, and `d ∈ minimalReps cs J ∅` of maximal length among
`minimalReps cs J ∅`. It proves `d = a⁻¹ w₀`.

1. `a⁻¹ w₀` is in `D(J,∅)`. An element of `standardSubgroup cs ∅` is `1`.
   For `b ∈ W_J`, also `b a⁻¹ ∈ W_J`, so `ℓ(b a⁻¹) ≤ ℓ(a)`. The complement
   law gives `ℓ(a⁻¹ w₀) = ℓ(w₀) − ℓ(a)` and
   `ℓ(b a⁻¹ w₀) = ℓ(w₀) − ℓ(b a⁻¹) ≥ ℓ(a⁻¹ w₀)`. This is the defining
   inequality of `IsMinimal cs J ∅`.
2. Maximality of `d` gives `ℓ(w₀) − ℓ(a) ≤ ℓ(d)`.
3. Taking the right factor `1` in `IsMinimal cs J ∅ d` shows that `d` is
   minimal in `W_J d`. Then `length_mul_of_left_minimal` gives
   `ℓ(a d) = ℓ(a) + ℓ(d)`.
4. The complement law at `x = a d w₀⁻¹` gives
   `ℓ(a) + ℓ(d) + ℓ(a d w₀⁻¹) = ℓ(w₀)`. With step 2, `ℓ(a d w₀⁻¹) = 0`.
   So `a d = w₀`, and `d = a⁻¹ w₀`.

`longestRepresentativeUnique_proof` chooses `w₀` of maximal length in the
finite group with `Finset.exists_max_image`. It chooses `a` of maximal
length in the finite set of elements of `W_J`, which contains `1`. The
supplied `w` satisfies the hypotheses of the helper. So does
`longestRep cs J`, by `longestRep_mem` and `length_le_longestRep`. Both
therefore equal `a⁻¹ w₀`, which proves `w = longestRep cs J`.

## Scope

The published constructions and the target pair are unchanged. The result
is intrinsic Coxeter uniqueness of the longest minimal representative. It
neither realizes relative roots or actual Levi subgroups nor proves the
longest-survivor criterion, the associated-subset laws or either finite
cancellation target.
