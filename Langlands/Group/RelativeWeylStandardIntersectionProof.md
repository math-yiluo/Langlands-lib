# Standard intersections at minimal double-coset representatives

`Langlands.Group.RelativeWeylIndexing.standardIntersection_proof` proves the
exact published proposition `standardIntersection cs` from
`Langlands.Group.RelativeWeylIndexingTargets`.

The parameters are `B : Type u`, `W : Type v`, `[Group W]`,
`M : CoxeterMatrix B`, and `cs : CoxeterSystem M W`, with independent
universes. For all `I J : Finset B` and `w : W` satisfying the published
whole-double-coset predicate `IsMinimal cs I J w`, it proves

\[
W_J\cap w^{-1}W_I w = W_K,\qquad
K=\{\,j\in J : w s_j w^{-1}\in W_I\,\}.
\]

Here the left side is the published `rightIntersection cs I J w`, that is,
`standardSubgroup cs J ⊓ conjugateStandardSubgroup cs I w⁻¹`, and `K` is the
published `intersectionSubset cs I J w`. There is no finiteness or
nonemptiness assumption on either type, and either subset may be empty. No
intersection, uniqueness, normal-form, reduced-word or exchange premise is
added.

## Provenance and dependencies

The original-source provenance of the target is recorded in the unchanged
`RelativeWeylIndexing.md` and `RelativeWeylIndexingTargets.md`: Aubert 1995,
printed pp.2180–2183, and Renard V.4.6(i), printed pp.120–121. The argument
implemented here is an internal Coxeter proof. No direct reading or
implementation of Carter is claimed.

The sole direct import is the published
`Langlands.Group.RelativeWeylMinimalityProof`. The proof uses its public
`left_minimal_of_simple`, `length_mul_of_left_minimal`,
`wordProd_mem_standard` and `exists_standard_word`, together with
`simple_left_exchange_append` from its published import
`Langlands.Group.RelativeWeylExchange`. That exchange lemma was proved from
the Coxeter presentation and inversion-sequence API and holds for arbitrary,
not necessarily reduced, words. The published `isMinimal_inv` and
`simple_mem_standardSubgroup` come from `Langlands.Group.RelativeWeylIndexing`.
Neither the minimum criterion theorem nor the uniqueness theorem
`minimalRepresentativeUnique_proof` is used.

The remaining inputs are Mathlib's reduced-word existence, the word-length
bound, the simple-multiplication length dichotomy
`length_simple_mul_ne`, `length_one`, `length_eq_zero_iff`, subgroup
closure and membership laws, list erasure lemmas, the `group` normalization
tactic, and natural-number strong induction and arithmetic.

## Membership reformulations

Two private helpers unfold the published constructions.
`mem_intersectionSubset_iff` states that `j ∈ intersectionSubset cs I J w`
exactly when `j ∈ J` and `w s_j w⁻¹ ∈ W_I`. `mem_rightIntersection_iff`
states that `x ∈ rightIntersection cs I J w` exactly when `x ∈ W_J` and
`w x w⁻¹ ∈ W_I`, since conjugation by `w⁻¹` sends `a` to `w⁻¹ a w`.

## A descent inside `W_J`

The private helper `exists_left_descent_of_mem` shows that every
`x ∈ W_J` with `x ≠ 1` has some `j ∈ J` with `ℓ(s_j x) < ℓ(x)`. Otherwise,
since simple multiplication never preserves length, `ℓ(x) < ℓ(s_j x)` for
every `j ∈ J`. The public `left_minimal_of_simple` then makes `x` of least
length in `W_J x`. Testing it at `x⁻¹ ∈ W_J` gives `ℓ(x) ≤ ℓ(1) = 0`, so
`x = 1`. No reduced-word-in-`J` lemma is needed.

## The key exchange step

The private helper `conj_simple_mem_of_left_descent` takes the minimal
`w`, an element `x ∈ W_J` with `y = w x w⁻¹ ∈ W_I`, and `j ∈ J` with
`ℓ(s_j x) < ℓ(x)`. It proves `w s_j w⁻¹ ∈ W_I`.

Put `v = w⁻¹`. The published `isMinimal_inv` makes `v` a whole-double-coset
minimum for `(J, I)`. Testing it with the identity on the right shows that
`v` has least length in `W_J v`. Since `x` and `s_j x` lie in `W_J`,
`length_mul_of_left_minimal` gives

\[
\ell(xv)=\ell(x)+\ell(v),\qquad \ell(s_j x v)=\ell(s_j x)+\ell(v),
\]

so `s_j` is a left descent of `xv`. Choose a reduced word `β` for `v` and,
by `exists_standard_word`, a word `α` with letters in `I` for `y`. Then
`π(β ++ α) = v y = x v`. Apply `simple_left_exchange_append` to `β ++ α`.

* If the erased letter lies in `β`, cancelling `π α` gives
  `s_j v = π(β.eraseIdx k)`. Hence `ℓ(s_j v) ≤ |β| - 1 < ℓ(v)`. This
  contradicts minimality of `v`, tested at `s_j ∈ W_J` on the left and the
  identity on the right.
* If the erased letter lies in `α`, put `z = π(α.eraseIdx k)`. Its letters
  lie in `I`, so `z ∈ W_I` by `wordProd_mem_standard`. The exchange equation
  is `s_j v y = v z`. Multiplying on the left by `w` and on the right by
  `y⁻¹` gives
  \[
  w s_j w^{-1} = z\,y^{-1}\in W_I.
  \]

Thus the first case is impossible and the second places `j` in `K`.

## Induction and the two inclusions

The private helper `mem_standard_of_conj_mem` proves, by strong induction
on `n = ℓ(x)`, that every `x ∈ W_J` with `w x w⁻¹ ∈ W_I` lies in `W_K`.
The case `x = 1` is immediate. Otherwise take the descent `j ∈ J` of the
preceding section. The exchange step gives `j ∈ K`. The shorter element
`x' = s_j x` still lies in `W_J`, and

\[
w x' w^{-1} = (w s_j w^{-1})(w x w^{-1}) \in W_I.
\]

The induction hypothesis gives `x' ∈ W_K`, so `x = s_j x' ∈ W_K`.

The theorem `standardIntersection_proof` combines two inclusions by
`le_antisymm`. The inclusion `rightIntersection ≤ W_K` is the induction
lemma applied at `n = ℓ(x)`. For the reverse inclusion, `Subgroup.closure_le`
reduces to generators: for `j ∈ K`, `s_j ∈ W_J` because `j ∈ J`, and
`w s_j w⁻¹ ∈ W_I` by the definition of `K`.

## Scope

The published constructions and the target pair are unchanged. The result
is the intrinsic Coxeter-subgroup theorem. It supplies no realization of
actual relative roots, rational-point Levi subgroups or their intersections,
and it discharges no representation-theoretic, topology, normalization or
classification premise. The cancellation, longest-representative and
actual-family comparison targets remain separate obligations.
