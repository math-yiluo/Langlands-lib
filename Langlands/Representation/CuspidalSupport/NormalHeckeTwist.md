# Maps out of ind_H^G ρ: Frobenius reciprocity and character twists

Author: Worker 1826.

This is a supporting module for the proofs of Renard VI.4.4 (the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement`), in namespace
`Langlands.CuspidalSupport.NormalHecke`. It continues the published modules
`Langlands.Representation.CuspidalSupport.NormalSubgroupHecke` (Worker 1789) and
`Langlands.Representation.CuspidalSupport.NormalHeckeGrading`. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, printed
pp.155–159 / PDF pp.161–165, where the action of End(ind ρ) on Hom(ind ρ, π) and the
twists π ⊗ ω by unramified characters are used. All declarations are internal
helpers; none of them is a statement of the book.

## Setting

G is a topological group, H a subgroup with `hH : IsOpen H`, ρ a smooth complex
representation of H (in its own carrier universe), and `inducedRep H ρ` the published
compact induction ind_H^G ρ. For w ∈ ρ, f_w is the published `unitFunction`:
it is supported on H, with f_w(h) = ρ(h) w.

## Frobenius reciprocity

- `inducedHomEquiv H ρ hH B` (**definition**, internal): for a smooth representation B
  of G in the carrier universe of ind_H^G ρ, the ℂ-linear bijection between maps
  T : ind_H^G ρ → B and H-equivariant maps ρ → B|_H, given by
  T ↦ (w ↦ T(f_w)). The inverse sends φ to f ↦ ∑ᶠ_{H x} B(x⁻¹) φ(f(x)), the published
  `cosetSum`. Both inverse laws are the published `cosetSum_resIntertwining_comp`,
  `cosetSum_unitMap` and `cosetSum_comp_unitMap` of
  `Langlands.Representation.Induction.OpenAdjunction`. This is the same
  construction as the published Frobenius adjunction for open subgroups, stated
  directly as a bijection of Hom spaces, so that ρ need not live in the carrier
  universe of B.
- `inducedHomEquiv_apply`: the forward map is T ↦ (w ↦ T(f_w)) (by `rfl`).
- `induced_hom_ext`: two maps out of ind_H^G ρ that agree on every f_w are equal
  (injectivity of `inducedHomEquiv`).
- `liftIntertwiningEquiv H ρ π` (**definition**, internal): for a smooth
  representation π of G, H-equivariant maps from ρ into the restriction to H of the
  carrier lift of π (the published `SmoothRep.universeLiftFunctor`) correspond to
  maps ρ → π|_H (the published `SmoothRep.restrictSubgroup`), by composing with
  `ULift.down`.
- `inducedLiftHomEquiv H ρ hH π` (**definition**, internal): the composite of the two
  previous bijections, Hom(ind_H^G ρ, lift π) ≃ Hom_H(ρ, π|_H).
  `hom_inducedLiftHomEquiv_apply`: it sends T to w ↦ T(f_w), read in π.
- `rank_inducedLiftHom`: hence the ℂ-rank of Hom(ind_H^G ρ, lift π) is the rank of
  Hom_H(ρ, π|_H), raised to the carrier universe of G (`Cardinal.lift`). This is the
  multiplicity m of VI.4.4.

## Functions supported on one coset

- `eq_translate_unitFunction`: a compactly induced function F vanishing at every x
  with x g₀⁻¹ ∉ H is the translate by g₀⁻¹ of f_v, v = F(g₀). Both vanish off H g₀,
  and at x = h g₀ (h ∈ H) both equal ρ(h) F(g₀), by the published `eval_mul_left`.
- `hom_of_support`: for such F and a map T : ind_H^G ρ → B,
  T(F) = B(g₀⁻¹) T(f_{F(g₀)}), by the previous lemma and G-equivariance of T.

## Twists by a character trivial on H

Let ω : G → ℂˣ be a character with open kernel (so `B.twist ω hω`, the published
twist of `Langlands.Representation.Category.Twist`, is B ⊗ ω, acting by
g ↦ ω(g) B(g)), and assume `hωH : H ≤ ker ω`.

- `twist_representation_apply`: (B ⊗ ω)(g) v = ω(g) B(g) v (by `rfl`).
- `twist_comp_subtype`: the restrictions of B ⊗ ω and B to H are equal, since ω is
  trivial on H.
- `twistRestrictEquiv` (**definition**, internal): consequently H-equivariant maps
  ρ → (B ⊗ ω)|_H and ρ → B|_H are the same linear maps.
- `twistHomEquiv ρ hH ω hω hωH B` (**definition**, internal): the linear bijection
  Φ : Hom(ind_H^G ρ, B ⊗ ω) ≃ Hom(ind_H^G ρ, B), defined as Frobenius reciprocity for
  B ⊗ ω, followed by `twistRestrictEquiv` and the inverse of Frobenius reciprocity
  for B. `hom_twistHomEquiv_unitFunction`: Φ(φ)(f_w) = φ(f_w) for every w.
- `hom_twistHomEquiv_of_support`: if F vanishes off H g₀, then
  Φ(φ)(F) = ω(g₀) φ(F). By `hom_of_support` for both maps,
  Φ(φ)(F) = B(g₀⁻¹) φ(f_v) and φ(F) = ω(g₀⁻¹) B(g₀⁻¹) φ(f_v), with v = F(g₀).
- `twistHomEquiv_comp` (**the twist law**): let p : G → ι be a degree for H in the
  sense of the published `IsDegree` (ι an additive commutative group), α an
  endomorphism of ind_H^G ρ in the published `component H ρ hH p a`, and g₀ with
  p(g₀) = a. Then for every φ : ind_H^G ρ → B ⊗ ω,
  Φ(α ≫ φ) = ω(g₀)⁻¹ (α ≫ Φ(φ)), where α ≫ φ is "first α, then φ". By
  `induced_hom_ext` it suffices to compare both sides on f_w. The function α(f_w)
  vanishes at every x with x g₀⁻¹ ∉ H, since then p(x) ≠ a; so the right side is
  ω(g₀)⁻¹ ω(g₀) φ(α(f_w)) by `hom_twistHomEquiv_of_support`, which is the left side
  by `hom_twistHomEquiv_unitFunction`.

## Relation to the source

Renard identifies Hom(ind ρ, π) with Hom_{⁰G}(ρ, π) by Frobenius reciprocity and
compares the actions of the homogeneous elements of End(ind ρ) on Hom(ind ρ, π) and
Hom(ind ρ, π ⊗ ω). Here this comparison is the explicit bijection Φ, which is
the identity on Frobenius data; the twist law says that Φ intertwines the action of a
homogeneous element of degree a up to the scalar ω(g₀)⁻¹, for any g₀ of degree a.
