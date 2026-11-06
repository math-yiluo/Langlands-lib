# The cone decay from a character decay on the opposite chart

Lean module: `Langlands.Representation.Plancherel.ParabolicIntertwiningCharacterDecay`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1.1, printed pp. 277–281 (PDF pp. 43–47), proves convergence
of the standard intertwining integral by bounding coefficients of the inducing representation by
a power of the height of the Levi component `m_P(x)`, and showing that on a cone of characters
`δ^{1/2} χ` decays at `m_P(x)` faster than any power of `‖x‖`. The module
`ParabolicIntertwiningConeReduction` names the combined estimate (with the coefficient envelope
`‖m‖ ^ d`) `ParabolicOppositeConeDecay`. This module names the estimate without the envelope,
`ParabolicOppositeCharacterDecay`, and proves that it implies `ParabolicOppositeConeDecay`: the
height of the Levi projection of `p` with `x = p κ`, `κ` in a compact open subgroup, is at most a
constant times the height of `x`, so `‖m‖ ^ d` is absorbed by raising the decay exponent by `d`.
The argument is derived from Library results and is not transcribed from the source.

## Setting and notation

The data are those of the host statement as in `ParabolicIntertwiningConeReduction`: a
nonarchimedean local field `F`; a smooth affine group `G` of finite type over `F` whose point
group `G(F)` is locally compact and nonarchimedean (`exists_rationalMatrixNorm_projection_le`
assumes neither); a parabolic root presentation `r` of `p : P ⟶ G` with Levi `l : M ⟶ P`
(`M.X.left` affine, except in `exists_rationalMatrixNorm_projection_le`), and a geometric
unipotent radical `hn` of `n : U ⟶ P`;
subgroups `Ppt`, `Upt`, `U'pt` of `G(F)` with `Ppt` and `Upt` identified with the actual points
of `P` and `U` by `hPpt`, `hUpt`; `Mpt = parabolicLeviPointSubgroup p l`; a semidirect
decomposition `h : IsSemidirectDecomposition Ppt Mpt Upt` with closed `Upt` (`hU`); an open
subgroup `K` of `G(F)`. `Ū(F) = parabolicOppositeRadicalPoints r`,
`ν = parabolicLeviRationalNormCharacters r`, and for a representation `ρ₀` of `G` on a nonempty
`Fin N`, `‖g‖ = rationalMatrixNorm F ρ₀ g`. `C : ℝ → Set (unramifiedCharacters ν)` is any family
of character regions.

## Declarations

- `ParabolicOppositeCharacterDecay r h hU K ρ₀ C` (definition, a `Prop`; `U'pt` is an implicit
  argument): for every `s : ℝ` there is `R : ℝ` such that for every section
  `σ : (U ∩ U') \ U' → U'pt` of the quotient map with values in `Ū(F)`,
  `IsLocallyUniformQuotientDecayOn h hU K ν U'pt σ (fun _ => 1) (fun q => ‖σ q‖ ^ (-s)) (C R)`
  holds. Explicitly: near each `χ₀ ∈ C R` there are a neighbourhood and one constant `C₀` with
  `‖δ^{1/2}(m)‖ ‖χ(m)‖ ≤ C₀ ‖σ q‖ ^ (-s)` for every `χ` in the neighbourhood and every
  factorization `σ q = p κ` with `p ∈ Ppt`, `κ ∈ K`, where `m = h.projection p` and
  `δ^{1/2} = HaarModulus.closedHalfCharacter`.
- `exists_rationalMatrixNorm_projection_le`: if `K` is compact and `ρ₀` is closed, there is
  `c ≥ 0` such that `‖h.projection q‖ ≤ c ‖x‖` whenever `x = q κ` with `q ∈ Ppt` and `κ ∈ K`.
- `parabolicOppositeConeDecay_of_characterDecay`: if `K` is compact and `ρ₀` is closed, then
  `ParabolicOppositeCharacterDecay r h hU K ρ₀ C` implies
  `ParabolicOppositeConeDecay r h hU K ρ₀ C`.

## Proof as implemented

1. `exists_rationalMatrixNorm_projection_le`. Let `χ` be the cocharacter
   `splitComponentCocharacter ≫ a ≫ l ≫ p`. The public identifications
   `r.parabolic_eq_splitComponentCocharacter`, `r.range_comp_radical_eq hn` and
   `r.levi_eq_splitComponentCocharacter` rewrite `Ppt`, `Upt` and `Mpt` as `P(χ)(F)`, `U(χ)(F)`
   and `Z(χ)(F)`. For `q ∈ Ppt` with projection `m`, `m⁻¹ q ∈ Upt`
   (`h.projection_inv_mul_mem`), so `exists_rationalMatrixNorm_levi_le` (module
   `LeviProjectionHeight`) gives `‖m‖ ≤ C₁ ‖q‖`. The height is continuous
   (`continuous_rationalMatrixNorm`), hence bounded by some `B ≥ 1` on the compact `K`; with
   `q = x κ⁻¹`, submultiplicativity and inversion invariance of the height give
   `‖q‖ ≤ ‖x‖ B`, so `c = C₁ B`.
2. `parabolicOppositeConeDecay_of_characterDecay`. Given `d` and `s`, take `R` from the character
   decay at `s + d`. For a section `σ` with values in `Ū(F)` and `χ₀ ∈ C R`, take the
   neighbourhood and constant `C₀` from the character decay and use the constant `C₀ c ^ d`.
   For `σ q = p κ`, with `w = ‖σ q‖ ≥ 1` and `m` the projection of `p`, step 1 gives
   `‖m‖ ^ d ≤ (c w) ^ d`, and the character decay bounds `‖δ^{1/2}(m)‖ ‖χ(m)‖` by
   `C₀ w ^ (-(s + d))`. Multiplying, and using `w ^ (-(s + d)) (c w) ^ d = c ^ d w ^ (-s)`
   (`Real.rpow_natCast`, `Real.rpow_add`), gives the cone decay bound.

## Scope

The character decay itself is a hypothesis; for the regions of the host statement it needs the
relative root reflections and Langlands' lemma on the positive cone, which are not proved here.
The module does not complete the host theorem.
