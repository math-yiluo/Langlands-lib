# Completeness from discrete orbits and local cocompactness

`KP.completeSpace_of_discrete_orbits` is an abstract form of Kaletha–Prasad
(2023), Theorem 4.2.10 (completeness of the building), printed pp.171–172 /
PDF pp.202–203. Setting: a metric space `X` with an isometric action of a group
`Γ` (`IsIsometricSMul Γ X`). Hypotheses:

* `hcover`: for every `x₀` there is a compact `K ⊆ X` such that every `x` with
  `dist x x₀ < 1` is a translate `g • k` of a point `k ∈ K`;
* `hdisc`: for every `y` there is `ε > 0` such that `dist (g • y) y < ε`
  implies `g • y = y`.

Conclusion: `CompleteSpace X`.

Proof as implemented, following the source's argument without local
finiteness. Take a Cauchy sequence `u` and `N` with `dist (u j) (u N) < 1` for
`j ≥ N`. Write `u (j + N) = g j • k j` with `k j ∈ K`. A subsequence `k (φ j)`
converges to some `y ∈ K`. Let `ε` be given by `hdisc y`. Choose `M` such that,
from `M` on, the subsequence `u (φ i + N)` has oscillation `< ε/3` and
`dist (k (φ i)) y < ε/3`. Then for `i ≥ M` the triangle inequality gives
`dist (g (φ i) • y) (g (φ M) • y) < ε`. Discreteness at `y`, applied to
`g (φ M)⁻¹ g (φ i)`, gives `g (φ i) • y = g (φ M) • y =: x`. Hence
`dist (u (φ i + N)) x = dist (k (φ i)) y → 0`, and the Cauchy sequence `u`,
having a convergent subsequence, converges to `x`.

In the source, `K` is the closure of one chamber and `Γ` is `G(k)^0`. The radius
of `hcover` is 1, but any fixed positive radius would do. The orbit
discreteness is the second half of Lemma 4.2.11. The second assertion of
Theorem 4.2.10, about unions of facets, is not treated. The formulation is
derived and does not refer to buildings.

Author: Worker 1221.
