import Langlands.Representation.Archimedean.RealCharacterPairReducible

/-!
# The filtration of real standard modules for two adjacent characters

This module proves `RealCharacterPairFiltrationStatement`: the standard module of
`pre ++ character c :: character d :: post` with `Re t_c < Re t_d` has a filtration as in
`RealAdjacentFiltration`.

Write `ν = t_d - t_c` and `ε = pairParity c d`. In the generic case
(`ν ≠ ε + 2m + 1` for every `m : ℕ`) the filtration has the single piece `[d, c]`: the Frobenius
map `q₀ : K(pre ++ [d, c] ++ post) → K(pre ++ c :: d :: post)` with the generic multiplier
`genericMultiplier ν ε` is an intertwiner, and it is onto because the Frobenius map in the
opposite direction with the pointwise inverse multiplier is a right inverse (the generic
multiplier has no zeros on the parity class). The remaining case is the reducible one,
`RealCharacterPairReducible.realAdjacentFiltration_of_reducible`, and
`RealCharacterPairReducible.realCharacterPairFiltration_of_generic` combines the two.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterPairReducible

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open Langlands.LocalFactor.Archimedean

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData}

/-- **The generic case.** If `Re t_c < Re t_d` and `t_d - t_c ≠ pairParity c d + 2m + 1` for
every `m : ℕ`, the standard module of `pre ++ c :: d :: post` has the one-step filtration with
the piece `[d, c]`. -/
theorem realAdjacentFiltration_of_generic
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hlt : realBlockExponent (RealBlock.character c) < realBlockExponent (RealBlock.character d))
    (hne : ∀ m : ℕ, d.exponent - c.exponent ≠ (pairParity c d : ℂ) + 2 * m + 1) :
    RealAdjacentFiltration n pre post (RealBlock.character c) (RealBlock.character d) := by
  set ε := pairParity c d with hεdef
  have hε : ε = 0 ∨ ε = 1 := pairParity_eq c d
  have hν : 0 < (d.exponent - c.exponent).re := exponent_sub_re_pos hlt
  have hsym : IsSymmetric ε (sigma0 c d) (genericMultiplier (d.exponent - c.exponent) ε) :=
    isSymmetric_genericMultiplier _ hε
  have h0 := data_swap hn hsym
  have hB := data_unswap hn hsym
  have hrec0 : IsRecurrent (GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre) -
      GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre + 1) + 1) ε
      (genericMultiplier (d.exponent - c.exponent) ε) := by
    rw [exponent_swp_zero, exponent_swp_one]
    exact isRecurrent_genericMultiplier hν hε
  -- `q₀ ∘ B = id`
  have hinv : ∀ g, blockFrobMap h0 (blockFrobMap hB g) = g := fun g =>
    blockFrobMap_blockFrobMap_eq hB h0 g fun j _ hj1 _ _ =>
      absurd (mul_inv_cancel₀ (genericMultiplier_ne_zero hν hε hne j)) hj1
  let ws : Fin 1 → List RealBlock := fun _ => dc c d
  let q : ∀ j : Fin 1,
      kFiniteFunctions (realStandardModule n (pre ++ ws j ++ post)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n
          (pre ++ RealBlock.character c :: RealBlock.character d :: post)) (unitaryCompact ℝ n) :=
    fun _ => blockFrobMap h0
  refine ⟨1, ws, q, fun _ => Or.inl rfl, fun _ => isRealIntertwinerModulo_blockFrobMap h0 hrec0 _,
    ?_⟩
  refine eq_top_iff.2 fun g _ => Submodule.mem_iSup_of_mem (0 : Fin 1) ⟨blockFrobMap hB g, ?_⟩
  exact hinv g

end RealCharacterPairReducible

/-- **The filtration for two characters.** -/
theorem realCharacterPairFiltration : RealCharacterPairFiltrationStatement :=
  RealCharacterPairReducible.realCharacterPairFiltration_of_generic
    fun _ _ _ _ _ hn hlt hne => RealCharacterPairReducible.realAdjacentFiltration_of_generic hn hlt hne

end Langlands.Archimedean
