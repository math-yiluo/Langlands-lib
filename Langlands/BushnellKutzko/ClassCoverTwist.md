# Covering simple-character classes: conjugacy of twisted characters

This module proves `TwistConjugacyAt` (Bushnell and Kutzko, *Simple types in GL(N):
computing conjugacy classes* (1994), (2.8), (ii) ⇒ (iii), printed p. 121), in the case where the
twist coefficients `c_i` of (2.8) are `β_i - γ`.

Let `V` be finite-dimensional, `ψ_F` an additive character of `F` that is trivial on `𝔭_F` and
nontrivial on `𝔬_F`, and `k + 1 < n`. Let `[𝔄,n,k+1,γ]` be a simple stratum on the lattice chain
`L`, `ϑ` a pair of `Ĉ(𝔄,k,γ)`, and `P_i ∈ Ĉ(𝔄,k,β_i)` (`i = 1, 2`) pairs over simple strata
`[𝔄,n,k,β_i]` on `L` with `β_i ≡ γ (mod 𝔓^{-(k+1)})`, with the subgroup of `ϑ`, whose characters
are `ϑ ψ_{β_i-γ}`. If `β₂ ≡ x⁻¹ β₁ x (mod 𝔓^{-k})` for some
`x ∈ U(𝔄)`, then `P₁` and `P₂` are `U(𝔄)`-conjugate. Condition (ii) of (2.8) enters in the form used
in BK94's proof, as such an `x`. The proof shows more: `P₁` conjugated by the given `x` is `P₂`.

* `mem_centralizerUnits_of_elementAlgebra_eq_bot`: a scalar commutes with every unit.
* `simpleIntertwiningNeighborhood_subset`: for `γ` not a scalar, the neighbourhood
  `1 + 𝔔^{-(t+k₀)}𝔑_{k₀}` of BK93 (1.5.8) for `[𝔄,n,t,γ]` lies in the factor `Y` of BK93 (3.3.2) at
  index `t` (`simpleCharacterIntertwiningFactor`).
* `twistConjugacyAt`. The element `x` formally intertwines `[𝔄,n,k+1,γ]`, so by `simpleIntertwining`
  (BK93 (1.5.8)) it lies in `Y B_γ^× Y` (or commutes with `γ` when `γ` is a scalar). The transport
  `simpleCharacterPairs_conj_mem` puts `P₁` conjugated by `x` into `Ĉ(𝔄,k,β₂)`, whose pairs all have
  the same subgroup (`simpleCharacterPairs_eq_choiceImage`), so `x` normalizes the common domain
  `H^{k+1}(γ,𝔄)`. The values follow from `SimpleCharacterCovarianceStatement` (BK93 (3.3.9)) at `x`,
  `elementCharacter_conj`, and the triviality of `ψ_{x⁻¹β₁x-β₂}` on `U^{k+1}(𝔄)`.

The route differs from BK94, which obtains the normalization from BK93 (3.1.9).
