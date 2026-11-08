# Finite delta decompositions in compact induction from a character

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`, part of the proof of
`DeltaPairingStatement`.

Let `N` be a subgroup of a topological group `G` and `θ : N →* ℂˣ` a character. Let `x` be a
vector of `c-Ind_N^G θ` that is right invariant under a subgroup `K`.

- `isGood_of_eval_ne_zero`: if `x(c) ≠ 0`, then `c` is good for `K` (`IsGood N θ K c`).
  For `n ∈ N` with `c⁻¹ n c ∈ K`, covariance gives `x(n c) = θ(n) x(c)` and invariance gives
  `x(n c) = x(c)`. Hence `θ(n) = 1`.
- `exists_finset_orbits`: for an open `K` there is a finite set `s ⊆ G` such that
  - the coset images `orbit N K c` (`c ∈ s`) in `N \ G` are pairwise distinct;
  - they cover the projected support of `x`.
  The images are open and cover the compact projected support. A finite subcover gives
  representatives, and duplicate images are removed with
  `Finset.exists_subset_injOn_image_eq_of_surjOn`.
- `deltaVector' K hK c` is `deltaVector K hK c` when `c` is good and `0` otherwise, and
  `deltaVector'_of_good` unfolds it.
- `exists_delta_decomposition`: for a compact open subgroup `K` and right `K`-invariant `x`,
  there is a finite set `s` such that
  - every `c ∈ s` with `x(c) ≠ 0` is good;
  - `x = ∑_{c ∈ s} x(c) • deltaVector' K hK c`.

  The proof compares values at each `y ∈ G`.
  - If `x(y) = 0`: each summand with `x(c) ≠ 0` also vanishes at `y`. If `y = n c k`, then
    `x(y) = θ(n) x(c) ≠ 0`, a contradiction; otherwise the delta function vanishes at `y`.
  - If `x(y) ≠ 0`: `y` lies in `N c K` for exactly one `c ∈ s`, because the coset images are
    distinct. That summand gives `x(c) θ(n) = x(y)`, and the other summands vanish.
