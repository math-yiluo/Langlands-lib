# Formal intertwining and conjugacy of simple strata, from simple approximation

Source: Bushnell–Kutzko (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`,
(2.6.1), printed pp. 83–86 (PDF pp. 95–98), (2.6.2), printed p. 86 (PDF p. 98), with the
remark after (2.6.1) and (2.3.2), printed p. 57 (PDF p. 69).

## Results

- `SimpleConjugacy.IsPureElement.conj`: conjugation by a unit of `𝔄` preserves pure
  elements. It uses `normalizingUnits_conj` and `PureApproximation.valuation_conj`.
- `SimpleConjugacy.exists_conj_of_isPureElement`: assume
  `PureStratumSimpleApproximationStatement` (BK93 (2.4.1)(i)). Let `β₁, β₂` be elements of
  pure strata `[𝓛,n,r,β_i]` on the same chain. If some `g` carries an element of
  `β₂ + 𝔓^{−r}` into `β₁ + 𝔓^{−r}`, then a unit `u` of `𝔄` satisfies
  `u β₂ u⁻¹ ∈ β₁ + 𝔓^{−r}`.
- `simpleStratumConjugacy_of_approximation`:
  `PureStratumSimpleApproximationStatement → SimpleStratumConjugacyStatement`, in the
  same universes.

## Proofs

`exists_conj_of_isPureElement` is proved by induction on `k`. The claim for `k` is a
unit `u` with `u β₂ u⁻¹ ≡ β₁` modulo `𝔓^{−(n−1−k)}`, for `k ≤ n − 1 − r`.

- `k = 0` (`t = n − 1`): `exists_conj_of_pureOrNull` for the two pure cosets, as in
  `SimpleStratumConjugacyDepthOne`.
- `k → k + 1` (`t = n − 1 − k` to `t − 1`): replace `β₂` by `u β₂ u⁻¹`, which is pure
  (`IsPureElement.conj`), and `g` by `u g`. Apply `exists_conj_step` and compose the
  units.

Purity is used, not simplicity. This matches the remark after (2.6.1) in the source:
only equivalence to simple strata is needed, and by (2.4.1)(i) every pure stratum is
equivalent to a simple stratum.

For the first clause of `SimpleStratumConjugacyStatement`, equal orders give equal
filtrations (`LatticeChain.endFiltration_eq_of_order_eq`). `T` is then a pure stratum
on the chain of `S` (`Stratum.withChainAndLevel`, `Stratum.isSimple_withChainAndLevel`),
and `exists_conj_of_isPureElement` applies with `r = S.r`. A unit `u` of `𝔄` with
`u, u⁻¹ ∈ 𝔄` lies in `S.chain.unitFiltration 0` (`mem_unitFiltration_zero`).

For the second clause, let `y ∈ S.coset` with `g⁻¹ y g ∈ Z.coset`. Equivalence gives
equal filtrations and `S.r = T.r` (`StratumEquivalence.endFiltration_eq_of_equivalent`,
`StratumEquivalence.r_eq_of_equivalent`), and the order of `Z` gives
`Z.coset = 𝔓^{1−S.n}`. Since `T.n > T.r = S.n − 1`, `y ∈ T.coset ⊆ T.b + 𝔓^{1−T.n}`
and `g⁻¹ y g ∈ 𝔓^{1−S.n} ⊆ 𝔓^{1−T.n}`. This contradicts `conj_not_mem_of_isPure` for
the pure stratum `T`. The hypothesis `1 ≤ S.n` is not used.
