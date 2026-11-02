# Solomon's alternating intersection coefficient

`Langlands.Group.RelativeWeylIndexing.solomonCancellation_proof` proves the
exact published proposition `solomonCancellation cs` from
`Langlands.Group.RelativeWeylIndexingTargets`.

For every `B : Type u`, `W : Type v`, `[Group W]`, `[Fintype B]`,
`[Fintype W]`, Coxeter matrix `M` on `B` and `cs : CoxeterSystem M W`, it
states: for all `J K : Finset B` with `K ⊆ J`,

\[
\sum_{I \subseteq B} (-1)^{|I|}\, a_{J,I,K} = (-1)^{|K|}
\quad\text{in } \mathbb{Z}.
\]

Here `a_{J,I,K} = intersectionMultiplicity cs J I K` counts the `w` in
`minimalReps cs I J` (the `w` with `IsMinimal cs I J w`) for which
`rightIntersection cs I J w = W_J ∩ w⁻¹ W_I w` equals `standardSubgroup cs K`.
The sum runs over every `I : Finset B`, including `∅` and `Finset.univ`. The
theorem uses the published definitions without change, and its type is
`solomonCancellation cs` itself. Universes stay independent, and nothing
excludes empty `J`, empty `K`, `J = Finset.univ` or an empty index type `B`.

## Provenance and scope

The statement's source correspondence is in the unchanged
`RelativeWeylIndexingTargets.md`: Aubert 1995, printed p.2182, cites this
identity from Solomon through Carter, Proposition 2.7.7. No reading or
implementation of Solomon's or Carter's proof is claimed. The proof below is
an internal reduction to two other published finite-Coxeter results, Jacquet
cancellation and the longest-survivor criterion. It does not identify the
simple indices with actual relative roots and proves no Levi or
representation-theoretic statement.

The theorem has no premise beyond the target's. The intermediate theorem
`solomonCancellation_of_jacquetCancellation` takes `jacquetCancellation cs`
as a hypothesis. The final theorem discharges that hypothesis with the
published proof `jacquetCancellation_proof cs`.

## Dependencies

The module imports `Langlands.Group.RelativeWeylJacquetProof`,
`Langlands.Group.RelativeWeylStandardIntersectionProof`,
`Langlands.Group.RelativeWeylLongestSurvivorProof`,
`Langlands.Group.RelativeWeylIndexingTargets` and
`Mathlib.Algebra.BigOperators.Ring.Finset`. The published results used are:

* `jacquetCancellation_proof` (in `RelativeWeylJacquetProof`): the exact
  proof of `jacquetCancellation cs`. For `w` with `IsMinimal cs J ∅ w` and
  `K ⊆ J`, the alternating sum over `I ⊆ positiveSimpleSet cs w` of the
  indicator of `simpleImage cs w I ∩ J = K` is `(-1)^|K|` if
  `MapsIntoSimple cs w (positiveSimpleSet cs w) J`, and `0` otherwise.
* `simple_reflection_injective` (in `RelativeWeylSimpleInjective`, imported
  through `RelativeWeylJacquetProof`): with `[Fintype B]`, `cs.simple` is
  injective.
* `standardIntersection_proof` (in `RelativeWeylStandardIntersectionProof`):
  for `w` with `IsMinimal cs I J w`, `rightIntersection cs I J w` is
  `standardSubgroup cs (intersectionSubset cs I J w)`.
* `longestSurvivor_proof` (in `RelativeWeylLongestSurvivorProof`): for `w`
  with `IsMinimal cs J ∅ w`, `MapsIntoSimple cs w (positiveSimpleSet cs w) J`
  holds iff `w = longestRep cs J`. `mem_positiveSimpleSet` from the same
  module unfolds `i ∈ positiveSimpleSet cs w` to `ℓ(w) < ℓ(w s_i)`.
* From `RelativeWeylMinimalityProof`: `minimalityLengthCriterion_proof`
  (`IsMinimal cs I J w` iff `ℓ(w) < ℓ(s_i w)` for `i ∈ I` and
  `ℓ(w) < ℓ(w s_j)` for `j ∈ J`), `left_minimal_of_simple` (if
  `ℓ(w) < ℓ(s_i w)` for all `i ∈ I`, then `ℓ(w) ≤ ℓ(a w)` for all `a ∈ W_I`)
  and `length_mul_of_left_minimal` (if `w` is minimal in `W_I w` and
  `a ∈ W_I`, then `ℓ(a w) = ℓ(a) + ℓ(w)`).
* From `RelativeWeylIndexing`: `isMinimal_inv` (`IsMinimal cs I J w` gives
  `IsMinimal cs J I w⁻¹`), `simple_mem_standardSubgroup`, `mem_minimalReps`
  and `longestRep_mem`.
* From Mathlib: the Coxeter length lemmas `length_simple`, `length_one`,
  `length_inv`, `length_eq_zero_iff`, `length_eq_one_iff`,
  `length_simple_mul`, `length_mul_simple`, `simple_mul_simple_self` and
  `inv_simple`; and the finite-sum lemmas `Finset.natCast_card_filter`,
  `Finset.mul_sum`, `Finset.sum_comm` and `Finset.sum_subset`.

## New lemmas

All of these are public, in namespace `Langlands.Group.RelativeWeylIndexing`.
Write `ℓ` for `cs.length`, `s_i` for `cs.simple i` and `W_I` for
`standardSubgroup cs I`.

* `mem_of_simple_mem_standardSubgroup` (`[Fintype B]`): if `s_k ∈ W_I`, then
  `k ∈ I`. Proof by contradiction, assuming `k ∉ I`. For `i ∈ I` we have
  `i ≠ k`, so `s_i ≠ s_k` by injectivity. Hence `s_i s_k ≠ 1` and
  `ℓ(s_i s_k) ≠ 0`. Since `ℓ(s_i s_k)` is `ℓ(s_k) ± 1`, it equals `2`, so
  `ℓ(s_k) < ℓ(s_i s_k)`. By `left_minimal_of_simple`, `ℓ(s_k) ≤ ℓ(a s_k)` for
  every `a ∈ W_I`. Taking `a = s_k` gives `1 ≤ ℓ(1) = 0`, a contradiction.
* `exists_simple_of_mem_standardSubgroup` (`[Fintype B]`): an `a ∈ W_I` with
  `ℓ(a) = 1` equals `s_i` for some `i ∈ I`. Mathlib's `length_eq_one_iff`
  gives `a = s_i`; the previous lemma gives `i ∈ I`.
* `standardSubgroup_injective` (`[Fintype B]`): `W_Q = W_K` implies `Q = K`,
  by the first lemma in both directions.
* `exists_conj_simple_eq_of_isMinimal` (`[Fintype B]`): if
  `IsMinimal cs I J w`, `j ∈ J` and `a = w s_j w⁻¹ ∈ W_I`, then `a = s_i` for
  some `i ∈ I`. Specializing minimality to `b = 1` makes `w` minimal in
  `W_I w`, so `length_mul_of_left_minimal` gives `ℓ(w s_j) = ℓ(a) + ℓ(w)`.
  The minimality criterion gives `ℓ(w) < ℓ(w s_j)`, so
  `ℓ(w s_j) = ℓ(w) + 1` and `ℓ(a) = 1`. The previous lemma finishes.
* `intersectionSubset_eq_simpleImage_inter` (`[Fintype B]`): if
  `IsMinimal cs I J w`, then
  `intersectionSubset cs I J w = simpleImage cs w⁻¹ I ∩ J`. For `j ∈ J` with
  `w s_j w⁻¹ ∈ W_I`, the previous lemma gives `i ∈ I` with
  `w s_j w⁻¹ = s_i`, that is `w⁻¹ s_i w = s_j`. Conversely
  `w⁻¹ s_i w = s_j` with `i ∈ I` gives `w s_j w⁻¹ = s_i ∈ W_I`.
* `isMinimal_iff_subset_positiveSimpleSet` (`[Fintype B]`):
  `IsMinimal cs I J w` holds iff `IsMinimal cs ∅ J w` and
  `I ⊆ positiveSimpleSet cs w⁻¹`. Apply `minimalityLengthCriterion_proof` on
  both sides. The right-hand conditions agree; the left-hand condition
  `ℓ(w) < ℓ(s_i w)` is `ℓ(w⁻¹) < ℓ(w⁻¹ s_i)`, because
  `ℓ(w⁻¹ s_i) = ℓ((w⁻¹ s_i)⁻¹) = ℓ(s_i w)` and `ℓ(w⁻¹) = ℓ(w)`.
* `inner_sum_eq_jacquet_sum` (`[Fintype B]`): if `IsMinimal cs ∅ J w`, then

  \[
  \sum_{I \subseteq B} [\,\texttt{IsMinimal cs I J w} \wedge
    \texttt{rightIntersection cs I J w} = W_K\,]\,(-1)^{|I|}
  = \sum_{I \subseteq \texttt{positiveSimpleSet cs } w^{-1}}
    [\,\texttt{simpleImage cs } w^{-1} I \cap J = K\,]\,(-1)^{|I|}.
  \]

  By the previous lemma, a term with `I` outside the powerset vanishes
  (`Finset.sum_subset`). For `I` in the powerset, the same lemma gives
  `IsMinimal cs I J w`. Then `standardIntersection_proof` and the
  intersection-subset lemma rewrite the intersection as
  `W_(simpleImage cs w⁻¹ I ∩ J)`. By `standardSubgroup_injective`, this equals
  `W_K` exactly when `simpleImage cs w⁻¹ I ∩ J = K`.
* `solomonCancellation_of_jacquetCancellation` (`[Fintype B]`,
  `[Fintype W]`): `jacquetCancellation cs` implies `solomonCancellation cs`.
  The main proof is described below.

## The main proof

`solomonCancellation_of_jacquetCancellation` fixes `J` and `K ⊆ J`.

1. Each term `(-1)^|I| · a_{J,I,K}` is rewritten as the sum over all
   `w : W` of `(-1)^|I|` when `IsMinimal cs I J w` and
   `rightIntersection cs I J w = W_K`, and `0` otherwise. This uses
   `Finset.filter_filter`, `Finset.natCast_card_filter` and `Finset.mul_sum`.
2. The two sums are exchanged by `Finset.sum_comm`.
3. For each `w`, the inner sum over `I` equals `(-1)^|K|` if
   `w = (longestRep cs J)⁻¹` and `0` otherwise.
   * If `IsMinimal cs ∅ J w`, `inner_sum_eq_jacquet_sum` turns the inner sum
     into the Jacquet sum at `w⁻¹`. The hypothesis applies there because
     `IsMinimal cs J ∅ w⁻¹` holds by `isMinimal_inv`. It gives `(-1)^|K|`
     when `MapsIntoSimple cs w⁻¹ (positiveSimpleSet cs w⁻¹) J` holds, and
     `0` otherwise. By `longestSurvivor_proof` at `w⁻¹`, that condition is
     `w⁻¹ = longestRep cs J`, that is `w = (longestRep cs J)⁻¹`.
   * Otherwise no `I` has `IsMinimal cs I J w`, by
     `isMinimal_iff_subset_positiveSimpleSet`, so the inner sum is `0`. Also
     `w ≠ (longestRep cs J)⁻¹`, because `longestRep_mem` and `isMinimal_inv`
     make `(longestRep cs J)⁻¹` satisfy `IsMinimal cs ∅ J`.
4. The outer sum over `w` of an indicator at the single element
   `(longestRep cs J)⁻¹` is `(-1)^|K|`.

`solomonCancellation_proof` applies this theorem to
`jacquetCancellation_proof cs`.

## Remarks

Injectivity of `cs.simple` is essential. Within this module it enters only
through `mem_of_simple_mem_standardSubgroup`, on which the length-one
identification and `standardSubgroup_injective` rely. The identity fails for
analogous data in which two indices share a reflection. Take `W = ℤ/2`, send
both indices of a two-element `B` to the generator, and let `J = K = B`. Then
the left side is `-1`, not `1`. Such data are not a Coxeter system, so the
injectivity proved for Coxeter systems supplies exactly what is needed.

`[Fintype W]` is used through `minimalReps`, `longestRep` and the sums over
`W`. `[Fintype B]` is used through the sum over `Finset B`,
`positiveSimpleSet`, `simpleImage` and `simple_reflection_injective`. When
`B` is empty, the only `J`, `K` and `I` are `∅`, and the argument above
specializes without change.
