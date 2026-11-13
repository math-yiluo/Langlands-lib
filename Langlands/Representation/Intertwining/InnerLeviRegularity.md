# Regularity in stages for Renard VII.3.5 (ii)

Author: Worker 115. Module
`Langlands.Representation.Intertwining.InnerLeviRegularity`.

This module proves the regularity claim of Renard VII.3.5 (ii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.5, printed pp.237–240 / PDF pp.243–246): if `σ` is `P₁P₂`-regular, then it is
`(P₁∩L)(P₂∩L)`-regular. Renard argues with the Bruhat-cell ideals `I^{P₂,w̄}_σ`
(printed p.238): he compares double cosets of `W_M\W_L/W_M` and `W_M\W_G/W_M`. The
Library's `IsPQRegular` is instead phrased through one quotient of the Jacquet module (see
below). So the Lean proof takes a different route. It builds a surjection between these
quotients, induced by the restriction `T f = f̃(1)` that Renard uses for the operator
identity. These are internal helpers derived for this proof.

## Setting

The section variables are those of `InnerLeviOperatorIdentity`:

- `P₁ = MN₁` and `P₂ = MN₂` in `G` with `P₁(F), P₂(F) ⊂ Q(F)`, where `Q = LU`;
- `P₁' = MN₁'` and `P₂' = MN₂'` in `L` with `Pᵢ'(F) = Pᵢ(F) ∩ L(F)`;
- canonical point topologies on `G(F)`, `L(F)` and `M(F)`, with `G(F)` and `L(F)` locally
  compact and nonarchimedean.

`emb : L(F) → G(F)` is the point map, and `Ψ₁ = leviInductionStagesIso` is induction in
stages for `P₁ ⊂ Q`.

Regularity is the published `IsPQRegular`: `I_σ + I^{PQ}_σ = ℂ[A(F)]`. Here `I^{PQ}_σ`
(`pqRegularityKernel`) is the kernel in `ℂ[A(F)]` of the action, through `a : A → M`, on
`r_Q^G i_P^G(σ) / F^{<1̄}_{PQ}(σ)`. The quotient is by the image `F^{<1̄}_{PQ}`
(`boundarySupportImage`) of the boundary vanishing subspace `F̃^{<1̄}_{PQ}(σ)`.

## Declarations

- `groupAlgebraKernel_le_of_surjective`: let `T : V → W` be a surjective linear map with
  `T(ρ(φ b) v) = ρ'(φ b)(T v)`. Then the kernel of `ℂ[B]` acting on `V` is contained in the
  kernel of `ℂ[B]` acting on `W`. Proof: induction on group-algebra elements shows that `T`
  intertwines the algebra actions; surjectivity does the rest.
  `groupAlgebraKernel_quotient_le` is the same statement for the induced map `V/S → W/S'`
  when `T(S) ⊆ S'`.
- `innerLeviHalfModulus`: the half modulus `c = δ_U^{1/2}` of `Q(F)` acting on `U(F)`,
  restricted to `L(F)` as a character `L(F) →* ℂˣ`.
- `innerStageRestriction`: Renard's `T : i_{P₁}^G(σ) → i_{P₁'}^L(σ)`, `T f = Ψ₁(f)(1)`, as
  a linear map. `innerStageRestriction_eval` gives the formula `T f(x) = c(x)⁻¹ f(emb x)`,
  from `leviInductionStagesIso_eval'` at `g = 1`.
- `innerStageRestriction_levi`: `T(emb(y) · f) = c(y) · (y · T f)` for `y ∈ L(F)`. Proof:
  evaluate both sides at `x`, apply the formula at `x` and at `x y`, and use
  multiplicativity of `c`.
- `innerStageRestriction_unipotent`: `T(w · f) = T f` for `w ∈ U(F)`. Proof: the
  covariance of `Ψ₁(f) ∈ i_Q^G(·)` under `w ∈ Q(F)` (`normalizedInductionFunctor_covariant`).
  The Levi projection of `w` is `1`, and the half character of `Q(F)` is trivial on `U(F)`,
  a union of compact subgroups (`closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups`).
- `innerStageRestriction_surjective`: `T` is onto. Every `φ ∈ i_{P₁'}^L(σ)` is `F(1)` for
  some `F ∈ i_Q^G(i_{P₁'}^L(σ))` (`normalizedInduction_eval_surjective`), and `F = Ψ₁(f)`
  with `f = Ψ₁⁻¹(F)`.
- `innerStageRestriction_mem_boundary`: `T` maps `F̃^{<1̄}_{P₁P₂}(σ)` into
  `F̃^{<1̄}_{P₁'P₂'}(σ)`. This follows from `mem_innerBoundaryVanishing_of_map` and the
  formula for `T`.
- `inverseHalfCharacter_mul_halfCharacter`: if `δ₁(h₁) = δ₂(h₂) δ₃(h₃)` for positive
  characters, then `δ₁(h₁)^{-1/2} δ₂(h₂)^{1/2} = δ₃(h₃)^{-1/2}` in `ℂ`.
- `closedRestrictCharacter_congr_elem`: the modulus of conjugation on a closed subgroup `U`
  depends only on the conjugating element of the ambient group, not on the subgroup it is
  viewed in.
- `innerLevi_inverseHalfModulus_mul`: for `m ∈ M(F)`,
  `δ_{P₂}(m)^{-1/2} c(m) = δ_{P₂'}(m)^{-1/2}`. Proof:
  `nestedParabolicPointDecomposition` gives `N₂(F) = N₂'(F) U(F)` with
  `N₂'(F) = L(F) ∩ N₂(F)`. The published modulus product `NestedParabolic.modulus_product`
  then gives `δ_{N₂}(m) = δ_U(m) δ_{N₂ ∩ L}(m)`. `GroupTransport.closedRestrictCharacter_transport`
  identifies the modulus of `N₂(F) ∩ L(F)` with that of `N₂'(F)`, transported through
  `leviPointsEquiv`, and the previous lemma concludes.
- `innerStageRestriction_descends`: for `n ∈ N₂(F)`, the classes of `T(n · f)` and `T f`
  agree in the `N₂'(F)`-coinvariants of `i_{P₁'}^L(σ)`. Proof: write `n = emb(y) w` with
  `y ∈ N₂'(F)` and `w ∈ U(F)`. Then `T(n · f) = c(y) · (y · T f)` with `c(y) = 1`
  (`halfModulus_eq_one_of_mem_innerRadical`), and `y` acts trivially on coinvariants.
- `innerStageJacquetMap`: the induced linear map `[f] ↦ [T f]` from the
  `N₂(F)`-coinvariants of `i_{P₁}^G(σ)` to the `N₂'(F)`-coinvariants of `i_{P₁'}^L(σ)`
  (`Jacquet.Localization.lift`).
- `smul_mk_transfer`: a linear-algebra identity used to compare the `M(F)`-actions on the
  two coinvariant spaces.
- `innerLevi_pqRegularityKernel_le`: `I^{P₁P₂}_σ ⊆ I^{P₁'P₂'}_σ`. Proof: the map `T̄ =
  innerStageJacquetMap` is surjective (`T` is, and coinvariant projections are). It
  commutes with the normalized actions of `M(F)` on `r_{P₂}^G i_{P₁}^G(σ)` and
  `r_{P₂'}^L i_{P₁'}^L(σ)`: for `m ∈ M(F)`,
  `T̄(δ_{P₂}(m)^{-1/2} [m · f]) = δ_{P₂}(m)^{-1/2} c(m) [m · T f] = δ_{P₂'}(m)^{-1/2} [m · T f]`,
  by `innerStageRestriction_levi` and `innerLevi_inverseHalfModulus_mul`. It maps
  `F^{<1̄}_{P₁P₂}` into `F^{<1̄}_{P₁'P₂'}` (`innerStageRestriction_mem_boundary`). Then
  `groupAlgebraKernel_quotient_le` applies.
- `innerLevi_isPQRegular`: if `σ` is `P₁P₂`-regular, it is `P₁'P₂'`-regular, because
  `ℂ[A(F)] = I_σ + I^{P₁P₂}_σ ⊆ I_σ + I^{P₁'P₂'}_σ`.
