# Relative intertwining for the induction step of BK93 (2.6.1)

This module contains the first computation in the induction step of the proof of BK93
(2.6.1). Source: Bushnell–Kutzko (1993), registered as
`bushnell-kutzko-1993-admissible-dual-gln`, printed pp. 84–85 (PDF pp. 96–97), using
(1.5.8), printed p. 44.

## Results

- `neighborhood_bounds`: an element `w` of the factor `1 + 𝔔^{−(t+k)}𝔑_k` of (1.5.8)
  (`Stratum.simpleIntertwiningNeighborhood`) for a simple stratum `[𝔄,n,t,γ]` satisfies
  `w − 1, w⁻¹ − 1 ∈ 𝔓` and `γw − wγ ∈ 𝔓^{−t}`. The proof is that of the private lemma
  of the same name in `SimpleStratumCorestrictionCongruenceProof`, stated with the
  commutator written out.
- `conj_inv_left`, `conj_inv_right`: for such a `w` and `b ∈ 𝔓^{−t}`,
  `w⁻¹(γ + b)w ≡ γ + (γw − wγ) + b` and `w(γ + b)w⁻¹ ≡ γ − (γw − wγ) + b` modulo
  `𝔓^{1−t}`. This is the "straightforward computation" written out on printed p. 85.
- `exists_centralizer_intertwining`: let `Γ = [𝔄,n,t,γ]` be simple and
  `b₁, b₂ ∈ 𝔓^{−t}`. Let `g` carry an element `y` of `γ + b₂ + 𝔓^{1−t}` into
  `γ + b₁ + 𝔓^{1−t}`. Then there are `δ` commuting with `γ`, an element `w`, and
  `z₁, z₂` with `w ≡ γ + (γz₁ − z₁γ) + b₂` and `δ⁻¹wδ ≡ γ − (γz₂ − z₂γ) + b₁` modulo
  `𝔓^{1−t}`.

## Proof of `exists_centralizer_intertwining`

The element `g` intertwines `Γ` with itself, so by `simpleIntertwining` (BK93 (1.5.8))
`g = w₁ δ w₂` with `w_i` in the neighborhood and `δ ∈ B^×`. Put
`w = w₁⁻¹ y w₁` and `z_i = w_i`. `conj_inv_left` gives the first congruence.
Since `δ⁻¹ w δ = w₂ (g⁻¹ y g) w₂⁻¹`, `conj_inv_right` gives the second. A tame
corestriction kills the commutators with `γ`
(`TameCorestriction.adjointMap_eq_zero`). In `SimpleStratumConjugacyStep` these
congruences therefore become the intertwining of the derived cosets in `B` by `δ`.
