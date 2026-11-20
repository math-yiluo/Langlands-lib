# Equivalent simple strata: `𝔅 + 𝔓` and the critical exponent

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`,
covering parts (i) and (ii) of Bushnell–Kutzko 1993, (2.1.4), printed p. 50, through the
lemma (2.1.3) on the same page.

**Dependence on the chain only through the filtration.** `adjointLattice_congr`,
`centralizerLattice_congr`, `criticalIndexSet_congr` and `criticalExponent_congr` record
that `𝔑_k(β)`, `𝔓^k ∩ B`, the critical index set and `k₀(β)` depend on a lattice chain only
through `n ↦ 𝔓^n`. Equivalent strata have the same filtration
(`endFiltration_eq_of_equivalent` in `StratumEquivalenceOrder`), so all quantities can be
computed on one chain.

**General lemmas** (lattice chains over any commutative ring `O`, in a `K`-vector space `V`
for a field `K` that is an `O`-algebra).
- `adjointLattice_eq_of_sub_mem` (BK93 (2.1.3)): if `β₁ - β₂ ∈ 𝔓^{-r}` and `m ≤ -r`, then
  `𝔑_m(β₁) = 𝔑_m(β₂)`, since for `x ∈ 𝔄` the difference
  `a_{β₁}(x) - a_{β₂}(x) = (β₁-β₂)x - x(β₁-β₂)` lies in `𝔓^{-r} ⊆ 𝔓^m`.
- `centralizerLattice_le_adjointLattice`: `𝔅 = 𝔄 ∩ B ⊆ 𝔑_m(β)`.
- `centralizerLattice_zero_of_bot`, `criticalIndexSet_eq_empty_of_bot`: for scalar `β`
  (`K[β] = K`), `𝔅 = 𝔄` and the critical index set is empty.
- `adjointLattice_le_of_criticalExponent_lt`: if `k₀(β) < -r` (and the critical index set
  is bounded above when `β` is not scalar), then `𝔑_k(β) ⊆ 𝔅 + 𝔓` for every `k ≥ -r`;
  otherwise `k` would be a critical index above the supremum `k₀`.
- `sup_eq_and_criticalExponent_eq`: for one chain, `β₁ - β₂ ∈ 𝔓^{-r}`, both critical
  exponents `< -r`, and each `β_i` either scalar or with a nonempty, bounded-above critical
  index set (hypotheses `h₁`, `h₂`). Then `𝔅₁ ⊆ 𝔑_{-r}(β₁) = 𝔑_{-r}(β₂) ⊆ 𝔅₂ + 𝔓` and
  symmetrically, so `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓`. The critical index sets coincide: for `k ≤ -r` the
  lattices `𝔑_k` agree, and for `k > -r` neither set contains `k`. Hence the critical
  exponents agree: both are `⊥` if both parameters are scalar, and both are the supremum of
  the common set if neither is. A scalar and a nonscalar parameter cannot occur together:
  by `h₁`, `h₂` the nonscalar one has a nonempty critical index set, while the scalar one has
  an empty one.

**Local-field part.**
- `criticalIndexSet_nonempty_bddAbove`: for a pure stratum whose parameter `b` is not
  scalar, the published `adjointExactness`, applied to the field `E = F[b]` (the actual
  `elementAlgebra`, with `β = b ∈ E`, `F[β] = E`, `β ∉ F`, and the normalizing hypothesis of
  `IsPure`), gives a nonempty, bounded-above critical index set.
- `sup_eq_and_criticalExponent_eq_of_equivalent`: BK93 (2.1.4)(i)–(ii) for equivalent simple
  strata, combining the above with `r_eq_of_equivalent` and `sub_mem_of_equivalent`.

The source deduces (2.1.4)(i)–(ii) from (2.1.3) in the same way; the separate treatment of a
scalar parameter is needed because `criticalExponent` is `⊥` exactly in that case.
