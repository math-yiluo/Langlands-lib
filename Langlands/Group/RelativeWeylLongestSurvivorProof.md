# The longest-survivor criterion for parabolic representatives

`Langlands.Group.RelativeWeylIndexing.longestSurvivor_proof` proves the exact
published proposition `longestSurvivor cs` from
`Langlands.Group.RelativeWeylIndexingTargets`.

For every `B : Type u`, `W : Type v`, `[Group W]`, `[Fintype B]`,
`[Fintype W]`, Coxeter matrix `M` on `B` and `cs : CoxeterSystem M W`, it
states: for all `J : Finset B` and `w : W` with `IsMinimal cs J ∅ w`,

\[
\texttt{MapsIntoSimple cs w (positiveSimpleSet cs w) J}
\iff w = \texttt{longestRep cs J}.
\]

So for a minimum `w` of its left coset `W_J w`, every simple reflection
`s_i` with `ℓ(w s_i) > ℓ(w)` satisfies `w s_i w⁻¹ = s_j` for some `j ∈ J`
exactly when `w` is the constructed longest member of `D(J,∅)`. The theorem
uses the published `IsMinimal`, `standardSubgroup`, `positiveSimpleSet`,
`MapsIntoSimple`, `minimalReps` and `longestRep` without change. Its type is
`longestSurvivor cs` itself. Universes stay independent, and nothing excludes
empty `J`, `J = Finset.univ` or an empty simple-index type `B`.

## Provenance and scope

The statement's source correspondence is in the unchanged
`RelativeWeylIndexingTargets.md` and `RelativeWeylIndexing.md`: Aubert 1995,
printed pp.2182–2183. The proof below is an internal Coxeter-group argument
and need not follow the source's route. It does not claim to implement
Carter's proof. It does not identify the simple indices with actual relative
roots, and it does not prove any Levi conjugation or representation-theoretic
statement. Because `MapsIntoSimple` compares reflections, it ignores root
signs (see the targets Markdown).

The theorem has no premise beyond the target's. In particular no
longest-element, uniqueness, exchange, root-positivity or
subgroup-identification hypothesis is assumed, and no sibling target
(`minimalRepresentativeUnique`, `standardIntersection`,
`longestRepresentativeUnique`) is used. Every needed Coxeter lemma is proved
in this file or is already published.

## Dependencies

The module imports only `Langlands.Group.RelativeWeylMinimalityProof`, which
brings in `Langlands.Group.RelativeWeylExchange` and the target module. The
published results used are:

* `simple_left_exchange_append` (in `RelativeWeylExchange`): when `s_i`
  shortens `π(α ++ β)` from the left, it erases one letter of `α` or one
  letter of `β`.
* `minimalityLengthCriterion_proof`: `IsMinimal cs J ∅ w` holds iff
  `ℓ(w) < ℓ(s_j w)` for all `j ∈ J` (the right-hand condition for `∅` is
  vacuous).
* `length_mul_of_left_minimal`: if `w` is minimal in `W_J w` and `a ∈ W_J`,
  then `ℓ(a w) = ℓ(a) + ℓ(w)`.
* `mem_minimalReps`, `longestRep_mem` and `length_le_longestRep` from
  `RelativeWeylIndexing`: `longestRep cs J` lies in `D(J,∅)` and has maximal
  length there.
* From Mathlib's Coxeter `Length` module: `exists_isReduced`,
  `length_wordProd_le`, `length_mul_le`, `length_inv`, `length_simple`,
  `length_eq_zero_iff`, the parity lemmas `length_mul_simple_ne` and
  `length_simple_mul_ne`, the dichotomy `length_mul_simple`, and
  `exists_rightDescent_of_ne_one` with `isRightDescent_iff`.

## New Coxeter lemmas

All of these are public, in namespace `Langlands.Group.RelativeWeylIndexing`.

* `mem_positiveSimpleSet` unfolds membership:
  `i ∈ positiveSimpleSet cs w ↔ ℓ(w) < ℓ(w s_i)`.
* `simple_left_exchange_mul` is exchange for a product of group elements. If
  `ℓ(s_i x y) < ℓ(x y)`, then either `ℓ(s_i x) < ℓ(x)`, or
  `s_i x y = x y'` with `ℓ(y') < ℓ(y)`. Proof: take reduced words `α` for `x`
  and `β` for `y`, and apply `simple_left_exchange_append`. If the erased
  letter is in `α`, cancel `π β` on the right; then `s_i x` is represented by
  a word of length `|α| - 1 = ℓ(x) - 1`. Otherwise `y' = π(β.eraseIdx k)` has
  length at most `|β| - 1 = ℓ(y) - 1`.
* `conj_simple_of_left_descent_mul_simple`, a form of Deodhar's lemma. Let
  `ℓ(w) < ℓ(s_j w)` for all `j ∈ J`, let `j ∈ J`, and let
  `ℓ(s_j w s_i) < ℓ(w s_i)`. Then `w s_i w⁻¹ = s_j`. Proof: apply
  `simple_left_exchange_mul` with `x = w` and `y = s_i`. The first case
  contradicts the hypothesis on `w`. In the second, `ℓ(y') < 1` gives
  `y' = 1`, so `s_j w s_i = w`, and rearranging gives the claim. The lemma
  needs no ascent hypothesis on `s_i`.
* `mapsIntoSimple_longestRep` is the reverse direction of the criterion. Let
  `v = longestRep cs J`; by `minimalityLengthCriterion_proof`, `v` is a left
  `J`-minimum. Take `i` with `ℓ(v s_i) > ℓ(v)`. Since `v` has maximal length
  in `D(J,∅)`, `v s_i ∉ D(J,∅)`. The minimality criterion then gives some
  `j ∈ J` with `ℓ(s_j v s_i) ≤ ℓ(v s_i)`, and parity makes this strict. The
  Deodhar lemma then gives `v s_i v⁻¹ = s_j`.
* `exists_full_descent_of_mapsIntoSimple`. Let `w` be minimal in `W_J w`
  and satisfy the survivor condition. Choose `a ∈ W_J` maximizing `ℓ(a w)`
  (`Finset.exists_max_image` over the finite filter of `W_J`). Every `s_i`
  is then a right descent of `a w`:
  - If `ℓ(w s_i) > ℓ(w)`, the condition gives `w s_i w⁻¹ = s_j` with
    `j ∈ J`, so `a w s_i = (a s_j) w` with `a s_j ∈ W_J`. Maximality gives
    `ℓ(a w s_i) ≤ ℓ(a w)`, and parity makes it strict.
  - Otherwise `ℓ(w s_i) < ℓ(w)`, and by `length_mul_of_left_minimal`,
    `ℓ(a w s_i) ≤ ℓ(a) + ℓ(w s_i) < ℓ(a) + ℓ(w) = ℓ(a w)`.
* `exists_suffix_of_full_descent`. If every `s_i` is a right descent of `u`,
  then every `x` admits `z` with `u = z x` and `ℓ(u) = ℓ(z) + ℓ(x)`. The
  proof is by induction on `n = ℓ(x)`. For `n = 0`, `x = 1` and `z = u`. For
  `n + 1`, choose a right descent `s_i` of `x` and write `x' = x s_i`, so
  `ℓ(x') = n`. The induction hypothesis gives `u = z x'` with lengths adding.
  Now `s_i` shortens `u⁻¹ = x'⁻¹ z⁻¹` from the left, so apply
  `simple_left_exchange_mul`. The first case would make `s_i x'⁻¹ = x⁻¹`
  shorter than `x'⁻¹`, which is false. In the second,
  `s_i u⁻¹ = x'⁻¹ y` with `ℓ(y) < ℓ(z)`. Then `u = y⁻¹ x`, and
  `ℓ(u) ≤ ℓ(y) + ℓ(x) ≤ ℓ(z) - 1 + n + 1 = ℓ(u)`, so `z := y⁻¹` works.
* `eq_of_full_descent`: at most one element has every simple reflection as a
  right descent. Apply the previous lemma both ways: `u = z v` with
  `ℓ(u) = ℓ(z) + ℓ(v)`, and `ℓ(v) = ℓ(z') + ℓ(u)`. Hence `ℓ(z) = 0`, so
  `z = 1` and `u = v`. No finiteness or longest-element package is used.

## The main proof

`longestSurvivor_proof` fixes `J` and a left `J`-minimum `w`.

* (`→`) Assume the survivor condition for `w`, and let
  `v = longestRep cs J`. Specializing `IsMinimal` to `b = 1` makes `w` and
  `v` left `J`-minima. `mapsIntoSimple_longestRep` gives the survivor
  condition for `v`. By `exists_full_descent_of_mapsIntoSimple` there are
  `a, b ∈ W_J` such that `a w` and `b v` both have every simple reflection as
  a right descent. By `eq_of_full_descent`, `a w = b v`. Put
  `c = b⁻¹ a ∈ W_J`, so `v = c w`. Two applications of
  `length_mul_of_left_minimal` give `ℓ(v) = ℓ(c) + ℓ(w)` and, from
  `w = c⁻¹ v`, `ℓ(w) = ℓ(c⁻¹) + ℓ(v) = ℓ(c) + ℓ(v)`. Hence `ℓ(c) = 0`,
  `c = 1` and `w = v`.
* (`←`) If `w = longestRep cs J`, this is `mapsIntoSimple_longestRep`.

`[Fintype W]` is used only through `minimalReps`, `longestRep` and the
maximal choice in `exists_full_descent_of_mapsIntoSimple`. `[Fintype B]` is
used only through `positiveSimpleSet`. Nothing requires `J` or `B` to be
nonempty. When `B` is empty, every condition over simple indices is
vacuous.
