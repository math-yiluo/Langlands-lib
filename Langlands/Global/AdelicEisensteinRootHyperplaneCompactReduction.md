# Eisenstein continuations with root-hyperplane singularities for every maximal compact

Module `Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction`
defines the proposition
`Langlands.Global.EisensteinRootHyperplaneCompactReductionStatement`, proves it
(`Langlands.Global.eisensteinRootHyperplaneCompactReduction`), and proves the
composite `Langlands.Global.eisensteinRootHyperplaneContinuation_of_premises`.

## Statements

`EisensteinRootHyperplaneCompactReductionStatement` is the implication

`GoodPositionIwasawaCompactStatement → EisensteinGoodPositionRootHyperplaneContinuationStatement →
EisensteinRootHyperplaneContinuationStatement`

(universe `u`). The target `EisensteinRootHyperplaneContinuationStatement` (module
`Langlands.Global.AdelicRootHyperplaneContinuationStatement`) is Bernstein–Lapid,
Theorem 2.3 (1) and (6), in the local form of the Corollary in §8.6, for an
arbitrary maximal compact `K` with `P(𝔸)K = G(𝔸)`. The premises are:

- `GoodPositionIwasawaCompactStatement` (module
  `Langlands.Global.AdelicGoodPositionIwasawaCompactStatement`): a maximal
  compact `K₀` in good position for some standard parabolic family, with
  `P(𝔸)K₀ = G(𝔸)`;
- `EisensteinGoodPositionRootHyperplaneContinuationStatement` (module
  `Langlands.Global.AdelicEisensteinGoodPositionRootHyperplaneReduction`): the
  target for compact subgroups in good position.

`eisensteinRootHyperplaneContinuation_of_premises` derives the target from five
premises: `EisensteinMeromorphicContinuationStatement`,
`LeadingCuspidalInjectivityStatement`, `LeviCuspFormPairingMajorantStatement`,
`EisensteinCuspidalTestRootHyperplaneStatement` and
`GoodPositionIwasawaCompactStatement`. It composes this reduction with
`eisensteinGoodPositionRootHyperplaneReduction`.

## Helper results

- `differentiable_exp_complexParameterPairing`: for a linear coordinate system
  `e` of `X^*(P) ⊗ ℂ`, `v ∈ Hom(X^*(P), ℝ)` and `c ∈ ℂ`, the function
  `s ↦ exp(c ⟨e s, v⟩)` is entire.
- `AdelicGroupPoints.IsMaximalCompactSubgroup.map_conj`: conjugates of maximal
  compact subgroups of `G(𝔸)` are maximal compact. Conjugation is a
  multiplicative homeomorphism.
- `AdelicGroupPoints.IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite`:
  for a maximal compact `K`, `K ∩ G(𝔸_∞)` equals the projection of `K` to
  `G(𝔸_∞)` (by `IsMaximalCompactSubgroup.mem_iff`).
- `map_infinite_map_conj_ofInfinite`: conjugating by an infinite point `b`
  conjugates the infinite projection by `b`.

## Proof of the reduction

Let `K` be the given maximal compact with `P(𝔸)K = G(𝔸)` and `φ` the given
automorphic form on `U(𝔸)M(F) \ G(𝔸)` for `K_∞ = K ∩ G(𝔸_∞)`.

1. The first premise gives `𝓕` and `K₀`. Both infinite factors are maximal
   compact in `G(𝔸_∞)`. `infiniteAdelicMaximalCompactConjugacy` gives
   `b ∈ G(𝔸_∞)` with `b K_∞ b⁻¹ = K₀,∞`.
2. Put `t = b⁻¹` (as an adelic point) and `K' = t⁻¹ K t`. By
   `IsIwasawaCompact.conjInv`, `P(𝔸)K' = G(𝔸)`, and `K'` is maximal compact. Its
   infinite projection is that of `K₀`.
3. The right translate `ψ = φ(· b)` is automorphic for `K₀,∞`
   (`IsAutomorphicFunctionOn.infiniteRightTranslate`). By
   `IsIwasawaCompact.eisensteinSeries_mul_conjInv`,
   `E_K(φ, λ)(g) = c₁(λ) · E_{K'}(ψ, λ)(g t)` for all `λ` and `g`, where
   `c₁(λ) = exp(-⟨λ, H_{K'}(t)⟩)` is the inverse of the height factor.
4. `IsAutomorphicFunctionOn.exists_parameterTwist_of_infinite_eq` compares
   `K'` and `K₀`, which have the same infinite projection. It gives a finite
   set `S` of height differences and inducing functions `cut v`, automorphic for
   `K₀,∞`, with
   `ψ_λ (K') = ∑_{v ∈ S} exp⟨λ, v⟩ · (cut v)_λ (K₀)`.
   For `λ` regular enough each Eisenstein series of `cut v` converges absolutely
   (`EisensteinAbsoluteConvergenceStatement.exists_summable_eisensteinTerm` with
   `eisensteinAbsoluteConvergence`). Then
   `IsIwasawaCompact.eisensteinSeries_eq_finset_sum_of_twist` gives
   `E_{K'}(ψ, λ) = ∑_v exp⟨λ, v⟩ · E_{K₀}(cut v, λ)`.
5. The second premise, for `K₀` and each `cut v`, gives continuations `EP_v` with
   domains `DP_v` and their local clearing data. Define
   `EP(λ)(g) = c₁(λ) · ∑_{v ∈ S} exp⟨λ, v⟩ · EP_v(λ)(g t)` and `DP = ⋂_v DP_v`.
   - *Meromorphy.* `DP` is open and dense in coordinates. Each summand is an
     entire function times a meromorphic one
     (`isMeromorphicInCoordinatesOn_univ`, `IsMeromorphicInCoordinatesOn.mul`),
     restricted to `DP` (`congr_mono`). The sum
     (`IsMeromorphicInCoordinatesOn.sum`) and the product with `c₁` are
     meromorphic with domain `DP`.
   - *Agreement.* Take the bound `B = ∑_v (max(R_v^{sum}, 0) + max(R_v^{EP}, 0))`,
     which dominates every convergence and agreement bound. For `B`-regular `λ`,
     steps 3 and 4 give `EP(λ) = E_K(φ, λ)`.
   - *Clearing.* Near `λ₀ = e s₀` take the clearing data `(S_v, m_v, W_v)` of
     every `EP_v`. Put `S' = ⋃_v S_v`, `M = ∑_v m_v` and `W = ⋂_v W_v`. For each
     `v`, `∏_{S'} = ∏_{S' ∖ S_v} · ∏_{S_v}`, and
     `(∏_{S'})^M = (∏_{S_v})^{M - m_v} (∏_{S' ∖ S_v})^M · (∏_{S_v})^{m_v}`. The
     first two factors are entire (`differentiable_centeredLinearProduct`). So
     `c₁ · ∑_v exp⟨·, v⟩ · (∏_{S_v})^{M - m_v} (∏_{S' ∖ S_v})^M · h_v` is
     holomorphic on `W` and equals `(∏_{S'})^M · EP` on `W ∩ DP`. The same `S'`,
     `M` and `W` serve every `g`, and `S' ⊆ r.unipotentRoots`.

## Provenance

The reduction to a compact subgroup in good position is the one explained in
the Markdown of `EisensteinAbsoluteConvergenceStatement`. Conjugation at the
infinite places and a finite change of compact at the finite places multiply
`E(φ, λ)` by exponentials of `λ` and replace `φ` by finitely many automorphic
inducing functions. Exponentials of linear forms are entire and nowhere zero, so
the continuation and its root-hyperplane clearing transfer. Bernstein and Lapid
(*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §2.1, p.190, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`) fix `K` in good
position from the start. This module removes that assumption from Theorem 2.3
(1), (6) in the form of `EisensteinRootHyperplaneContinuationStatement`.
