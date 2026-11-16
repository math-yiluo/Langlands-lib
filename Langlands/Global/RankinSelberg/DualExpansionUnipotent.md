# Periods over `N_K(F) \ N_K(𝔸)` and the last-column decomposition

Module `Langlands.Global.RankinSelberg.DualExpansionUnipotent`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

## The decomposition `N_(K+1) = 𝔸^K ⋊ N_K`

- `colHom : ColGroup F (Fin K) →* N_(K+1)(𝔸)` (last column), `padHom : N_K(𝔸) →* N_(K+1)(𝔸)`
  (`u ↦ diag(u, 1)`) and `topLeftHom : N_(K+1)(𝔸) →* N_K(𝔸)` (top-left block) satisfy the
  hypotheses of the Library's `LeftCosetSpace.Semidirect.normalizedPeriod_eq_iterated_of_compact`
  (`topLeftHom_padHom`, `topLeftHom_colHom`, `exists_colHom_eq`, `isEmbedding_colHom`,
  continuity, and compatibility with rational points: `padHom_mem_rational`,
  `topLeftHom_mem_rational`, `colHom_mem_rational_iff`).
- `mem_rationalSubgroup_unipotent_iff`: a point of `N_n(𝔸)` is rational exactly when its matrix
  is the image of a rational matrix.

## Periods

- `unipotentPeriod F K f`: the normalized integral `|E|⁻¹ ∫_E f` over the Library's chosen
  fundamental domain `E = unipotentFundamentalDomain F K` of `N_K(F)` in `N_K(𝔸)`.
- `unipotentFundamentalDomain_haar_lt_top`: `E` has finite Haar measure (its measure is the
  inverse of the nonzero quotient-mass normalizer, by compactness of `N_K(F) \ N_K(𝔸)`). This
  lemma was first published as `haar_unipotentFundamentalDomain_lt_top`. It was renamed because
  `WhittakerExpansionCore.WhittakerBasic` declares a different lemma with that full name.
- `unipotentPeriod_succ`: for continuous left `N_(K+1)(F)`-invariant `φ`, the period over
  `N_(K+1)` is the period over `N_K` of the torus integral over the last column:
  `UP_(K+1) φ = UP_K (u ↦ T_c φ(colHom c · padHom u))`.
- `unipotentPeriod_torusIntegral_comm` (Fubini for jointly continuous, periodic, bounded
  integrands) and `unipotentPeriod_tsum` (termwise integration of series with a uniform bound).
