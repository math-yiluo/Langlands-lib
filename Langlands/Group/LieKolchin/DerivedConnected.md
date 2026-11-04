# Connected derived subgroups for separately continuous group laws

Worker 277.

This module proves the topological input of the abstract Lie–Kolchin argument in
`Langlands.Group.LieKolchin.CommonEigenvector`. The group `G` carries an arbitrary
topology. No topological-group structure is assumed, because the Zariski topology on the
rational points of an algebraic group does not make multiplication jointly continuous.
The hypotheses are only these separate continuity conditions:

- `hmul`: every left translation `x ↦ a * x` is continuous;
- `hinv`: inversion is continuous;
- `hcomm`: every map `y ↦ ⁅a, y⁆ = a * y * a⁻¹ * y⁻¹` is continuous.

## Declarations

- `isConnected_commutator hmul hinv hcomm hΓ`: if the subgroup `Γ` has a preconnected
  underlying set, the commutator subgroup `⁅Γ, Γ⁆` is connected.

  Proof. Let `H = ⁅Γ, Γ⁆` and let `K` be the connected component of `1` in `H`.
  `K` is a subgroup. If `a, b ∈ K`, the left translate `a • K` is preconnected,
  lies in `H` and contains `a`. It therefore lies in the component of `a` in `H`,
  which is `K`, so `a * b ∈ K`. Inverses are handled the same way with the image
  `K⁻¹`, which contains `1`. Each generator `⁅x, y⁆` with `x, y ∈ Γ` lies in the
  image of `Γ` under `z ↦ ⁅x, z⁆`. This image is preconnected by `hcomm x`, lies in
  `H`, and contains `⁅x, 1⁆ = 1`, so it lies in `K`. Hence `H ≤ K`, and therefore
  `H = K` is connected.
- `isConnected_derivedSeries hmul hinv hcomm n`: if `G` is a preconnected space, every
  term `derivedSeries G n` is connected. The proof is induction on `n`, using
  `isConnected_commutator` at each step.
- `subset_of_finite_closed_cover`: a preconnected set `s` covered by finitely many closed
  sets `A i` (`i ∈ t`) that are pairwise disjoint on `s` lies entirely in each `A i₀` that it
  meets. The union of the other `A i` is closed. `s` is covered by `A i₀` and this union,
  and its intersection with both is empty. Preconnectedness forces `s` into one of the
  two, and the point of `s` in `A i₀` rules out the second.

## Provenance

These are internal lemmas for the rational-point proof of Lie–Kolchin. The first is a
rational-point, separately continuous analogue of J. S. Milne, *Algebraic Groups* (2017),
Corollary 6.19(b), printed p. 129: the derived group of a connected algebraic group is
connected. It is proved directly for an abstract group with the separate continuity
hypotheses above; nothing here depends on algebraic-group theory. The third lemma is the
finite closed-cover argument that the proof of Milne's Theorem 16.30 (printed
pp. 334–335) applies to the cosets of a closed finite-index stabilizer.
