import Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Character covariance under Shalika's fiber action: proof

At a fixed diagonal parameter `d`, Shalika's action of `u ∈ U_w⁺` translates the first
`U` factor on the right by the element `g` with matrix `p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹`
and the last factor on the left by `u`. Substituting `(z₁, z₂) ↦ (z₁ * g, u * z₂)`
preserves `μ.prod μ` by right invariance on the first factor and left invariance on the
last, and it turns the inverse character weight into `χ g * χ u` times the weight at the
translated point. Since `g` is the inverse of the monomial conjugate of `u`, this
constant is the inverse of the compatibility defect.
-/

namespace Langlands.Whittaker

open MeasureTheory
open Langlands.GeneralLinear HarmonicAnalysis

universe uF

/-- Pulling a test function back along Shalika's action of `u ∈ U_w⁺` multiplies its
character average at `d` by the inverse of the compatibility defect of `u` at `d`. -/
theorem bruhatFiberCharacterCovariance : BruhatFiberCharacterCovarianceStatement.{uF} := by
  intro p _ F
  let := F.canonicalNormedField
  intro n ψ w U P H M
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  intro μ _ _ _ _ α u d
  -- The element `g ∈ U` with matrix `p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹`.
  let g : U := ⟨permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * u.val⁻¹ *
      (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F.Carrier w)⁻¹,
    permutation_diagonal_conj_inv_mem_upperUnipotent (n + 1) F.Carrier w d u⟩
  let ι := Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w)
  -- The substitution `(z₁, z₂) ↦ (z₁ * g, ι u * z₂)` preserves `μ.prod μ`.
  have hmp : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight g) (MeasurableEquiv.mulLeft (ι u)))
      (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_mul_right μ g).prod (measurePreserving_mul_left μ (ι u))
  -- At the parameter `d` the action is this substitution.
  have hact : ∀ z : U × U,
      bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2)) = (z.1 * g, (d, ι u * z.2)) := by
    intro z
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [bruhatFiberAct_fst_val]
    change z.1.val * permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F.Carrier w)⁻¹ =
      z.1.val * (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F.Carrier w)⁻¹)
    simp only [mul_assoc]
  -- The defect is the quotient of the character values at `k = s * u * s⁻¹` and at `u`.
  have hu : permutation (n + 1) F.Carrier w * (ι u).val *
      (permutation (n + 1) F.Carrier w)⁻¹ ∈ upperUnipotent (n + 1) F.Carrier :=
    ((mem_permutationUnipotentPlus_iff _ _ _ _).mp u.property).2
  let k : U := ⟨permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * (ι u).val *
      (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d)⁻¹,
    monomial_conj_mem_upperUnipotent w d hu⟩
  have hdef : compatibilityDefect ψ n w (ι u) d =
      (standardCharacter ψ n k : ℂ) / (standardCharacter ψ n (ι u) : ℂ) :=
    compatibilityDefect_eq_div ψ n w hu d
  -- `g` is the inverse of `k`.
  have hgk : g * k = 1 := by
    apply Subtype.ext
    change permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F.Carrier w)⁻¹ *
      (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d * u.val *
        (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d)⁻¹) = 1
    group
  have hχgk : (standardCharacter ψ n g : ℂ) * (standardCharacter ψ n k : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hgk, map_one, Units.val_one]
  change ∫ z : U × U, α (bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2))) *
        ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ ∂(μ.prod μ) =
      (compatibilityDefect ψ n w (ι u) d)⁻¹ *
        ∫ z : U × U, α (z.1, (d, z.2)) *
          ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ ∂(μ.prod μ)
  rw [← hmp.integral_comp' (fun v : U × U => α (v.1, (d, v.2)) *
      ((standardCharacter ψ n v.1 : ℂ) * (standardCharacter ψ n v.2 : ℂ))⁻¹),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change α (bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2))) *
      ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ =
    (compatibilityDefect ψ n w (ι u) d)⁻¹ *
      (α (z.1 * g, (d, ι u * z.2)) *
        ((standardCharacter ψ n (z.1 * g) : ℂ) * (standardCharacter ψ n (ι u * z.2) : ℂ))⁻¹)
  rw [hact z, hdef, map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hk : (standardCharacter ψ n k : ℂ) ≠ 0 := (standardCharacter ψ n k).ne_zero
  have hι : (standardCharacter ψ n (ι u) : ℂ) ≠ 0 := (standardCharacter ψ n (ι u)).ne_zero
  have h₁ : (standardCharacter ψ n z.1 : ℂ) ≠ 0 := (standardCharacter ψ n z.1).ne_zero
  have h₂ : (standardCharacter ψ n z.2 : ℂ) ≠ 0 := (standardCharacter ψ n z.2).ne_zero
  rw [eq_inv_of_mul_eq_one_left hχgk]
  field_simp

end Langlands.Whittaker
