# Uniqueness of Coxeter parabolic double-coset minima

`Langlands.Group.RelativeWeylIndexing.minimalRepresentativeUnique_proof`
proves the exact published proposition `minimalRepresentativeUnique cs`
from `Langlands.Group.RelativeWeylIndexingTargets`.

The parameters are `B : Type u`, `W : Type v`, `[Group W]`,
`M : CoxeterMatrix B`, and `cs : CoxeterSystem M W`, with independent
universes. For all `I J : Finset B` and `w x y : W`, two members `x,y`
of the constructed `doubleCoset cs I J w` that both satisfy the published
whole-double-coset predicate `IsMinimal cs I J` are equal. There is no
finiteness or nonemptiness assumption on either type, and either subset
may be empty.

## Provenance and dependencies

The original-source provenance of the target is recorded in the unchanged
`RelativeWeylIndexing.md` and `RelativeWeylIndexingTargets.md`: the unique
minimum underlies Renard V.4.6(i), printed pp.120–121, and the
minimal-representative indexing in Aubert 1995, printed pp.2180–2183.
The argument implemented here is an internal Coxeter proof. No direct
reading or implementation of Carter is claimed.

The sole direct import is the published
`Langlands.Group.RelativeWeylMinimalityProof`. The proof uses its
`length_mul_of_left_minimal` and `length_mul_of_right_minimal`, together
with `simple_left_exchange` and `simple_left_exchange_append` from its
published import `Langlands.Group.RelativeWeylExchange`. Exchange was
proved there from the Coxeter presentation and inversion-sequence API;
it is not an added hypothesis. The minimum criterion theorem and the
minimum-existence helper are not invoked by this proof.

Additional inputs are subgroup closure induction, subgroup membership
laws, Mathlib's word products, reduced-word existence and reduced tails,
the simple-multiplication length dichotomy, the word-length bound, inverse
word products, and the equivalence between length zero and the identity.
The word-membership and word-generation helpers are reused from the
minimum-criterion module, where they are public shared helpers.

## Reduced words inside a standard subgroup

`wordProd_mem_standard` proves that a word whose letters lie in `I` has
product in `standardSubgroup cs I`. Conversely,
`exists_standard_word` uses subgroup closure induction to express every
element of that subgroup by such a word. Generators give singleton words,
multiplication concatenates them, and inversion reverses them because
simple reflections are involutions.

`reduce_standard_word` reduces any word on `I` while retaining letters
in `I`. Inductively reduce the tail of `i :: α` to a reduced word `β`.
If multiplication by `s_i` increases length, `i :: β` is reduced.
If it decreases length, `simple_left_exchange` deletes one letter from
`β` to express `s_i * πβ`. The descent length equation and the length of
the erased word show that this new word is reduced. In both cases its
product equals that of the original word and its letters still lie in
`I`. Combining the two constructions gives
`reduced_standard_word_exists`, an ambient reduced word on `I` for each
element of `W_I`. The reduction and reduced-word existence helpers are private.

## Removing the left word by exchange

The private helper `eq_of_minimal_word_relation` takes two minima `x,y`
of equal length and a relation

\[
(\pi\alpha)x=y(\pi\beta),
\]

where `α` is a reduced word on `I` and `β` is any word on `J`.
It proves `x=y` by induction on `α`. Whole-double-coset minimality
supplies left minimality of both elements and right minimality of `y`
by testing the other subgroup factor at the identity.

For `α=[]`, the relation becomes `x=y(πβ)`. Right length additivity at
`y` gives

\[
\ell(x)=\ell(y)+\ell(\pi\beta).
\]

Equal lengths force `ℓ(πβ)=0`, so `πβ=1` and `x=y`.

For `α=i::α'`, the tail is reduced. Left length additivity at `x`,
applied to both words, shows that `s_i` is a left descent of
`y(πβ)=(πα)x`. Choose a reduced word `η` for `y` and apply
`simple_left_exchange_append` to `η ++ β`.

* If exchange deletes a letter of `η`, cancellation of the unchanged
  factor `πβ` gives `s_i y=π(η.eraseIdx k)`. The word-length bound gives
  `ℓ(s_i y)≤|η|-1<ℓ(y)`, contradicting left minimality of `y` since
  `i∈I`.
* If exchange deletes a letter of `β`, cancelling the initial
  `s_i` from `(πα)x` gives
  `(πα')x=y π(β.eraseIdx k)`. All remaining right letters still lie in
  `J`, and the induction hypothesis gives `x=y`.

Thus induction removes the left word without any normal-form or
parabolic-intersection premise.

## Applying the helper to the published target

Write the two supplied double-coset memberships as

\[
x=a_x w b_x,\qquad y=a_y w b_y.
\]

Set `a=a_x a_y⁻¹ ∈ W_I` and `b=b_y⁻¹ b_x ∈ W_J`. Then `x=a y b`.
Minimality of `y` applied to `a,b`, and minimality of `x` applied to
their inverses, prove `ℓ(x)=ℓ(y)`.

Choose a reduced standard word `α` for `a` and a standard word `β`
for `b⁻¹`. The equation becomes

\[
(\pi\alpha)y=x(\pi\beta).
\]

The preceding helper, with its two minima interchanged, gives `y=x`,
and symmetry proves the required `x=y`.

The published constructions and target pair are unchanged. The two
existing standard-word helpers are exposed for reuse with their original
statements and proofs. The result proves intrinsic
Coxeter minimum uniqueness; it supplies no realization of relative
roots, actual Levi subgroups, parabolic intersections, or
representation-theoretic comparisons.
