# Base change of the opposite cocharacter

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. That proof uses
the opposite cocharacter `t ↦ λ(t)⁻¹` of `λ` both over `k` and after base
change to an algebraic closure. Everything here is derived from the Library's
cocharacter base change (`Dynamic.BaseChange`) and power maps of `𝔾_m`
(`Torus.Lattice`); no external result is used.

- `comp_powerHom x m`: on points, the power map
  `CommGroupScheme.groupHom (Gm.powerHom S m)` of `𝔾_m` is `x ↦ x ^ m`. This
  follows from `Gm.powerHom S m = m • 𝟙` and the Library's
  `comp_groupHom_zsmul`.
- `baseChangeCocharacter_powerHom b χ m`: for `b : S' ⟶ S`, base change of the
  cocharacter `t ↦ χ(tᵐ)` is `t ↦ χ_{S'}(tᵐ)`. Proof: compare on all points
  (`hom_ext_points`). The pullback point equivalence is injective and
  multiplicative, `baseChangePointsEquiv_baseChangeCocharacter` describes base
  change of cocharacters on points, and the comparison isomorphism of `𝔾_m` is a
  homomorphism, so it commutes with `m`-th powers.
- `powerHom_neg_one_comp_powerHom_neg_one χ`: taking the opposite twice gives
  `χ` back, since `(t⁻¹)⁻¹ = t` on points.
