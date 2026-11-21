import Langlands.Global.RankinSelberg.ComplexSmoothTranslateDensity

/-! # Unipotent equivariance of the smooth complex Whittaker extension -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerEquivariance

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound)
open ComplexWhittakerSmoothExtension (SmoothStandard finiteToSmooth compactProfile complexWhittakerSmoothExtension)
open ComplexWhittakerTranslateExtension (smoothTranslate complexWhittakerTranslateExtension)
open ComplexSmoothTranslateDensity (complexSmoothTranslateDensity)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Std" => Automorphic.complexStandardKFinite

/-- Every exact complex Whittaker identity evaluation extends to a smooth standard-module
functional with the exact unipotent character law and a finite-order compact difference bound. -/
def ComplexSmoothWhittakerEquivarianceStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∃ (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C ∧
    (∀ f : Std (r + 1) ds, ∀ g : G (r + 1), L (smoothTranslate g (finiteToSmooth f)) = B f g) ∧
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) ∧
    ∀ (F : SmoothStandard (r + 1) ds) (u : G (r + 1)), u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ →
      L (smoothTranslate u F) = complexWhittakerCharacter a u * L F

theorem complexSmoothWhittakerEquivariance : ComplexSmoothWhittakerEquivarianceStatement := by
  intro r ds a B hB
  obtain ⟨L, J, C, hC, hRestr, hBound⟩ := complexWhittakerSmoothExtension r ds a B hB
  have hValue := complexWhittakerTranslateExtension r ds a B hB L J C hC hRestr hBound
  refine ⟨L, J, C, hC, hValue, hBound, fun F u hu => ?_⟩
  let c := complexWhittakerCharacter a u
  obtain ⟨D, hD, hApprox⟩ := complexSmoothTranslateDensity (r + 1) ds F u J
  have hPos : 0 < C * D * (1 + ‖c‖) + 1 := by positivity
  apply sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _)))
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (C * D * (1 + ‖c‖) + 1)
  obtain ⟨f, hF, hU⟩ := hApprox δ (div_pos hε hPos)
  let f' := finiteToSmooth f
  have hp : L (smoothTranslate u f') = c * L f' := by
    change L (smoothTranslate u (finiteToSmooth f)) = c * L (finiteToSmooth f)
    rw [hValue, hRestr]
    simpa only [mul_one, c] using hB.1 f u hu 1
  have h₁ : ‖L f' - L F‖ ≤ C * (D * δ) := by
    rw [← map_sub]
    apply hBound
    rw [map_sub]
    exact hF
  have h₂ : ‖L (smoothTranslate u F) - L (smoothTranslate u f')‖ ≤ C * (D * δ) := by
    rw [norm_sub_rev, ← map_sub]
    apply hBound
    rw [map_sub]
    exact hU
  have hδ : (C * D * (1 + ‖c‖)) * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_le_iff₀ hPos, mul_comm (C * D * (1 + ‖c‖)) ε]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
  change ‖L (smoothTranslate u F) - c * L F‖ ≤ 0 + ε
  rw [zero_add]
  calc
    _ = ‖(L (smoothTranslate u F) - L (smoothTranslate u f')) + c * (L f' - L F)‖ := by
      rw [hp, mul_sub]
      ring_nf
    _ ≤ ‖L (smoothTranslate u F) - L (smoothTranslate u f')‖ + ‖c * (L f' - L F)‖ := norm_add_le _ _
    _ ≤ C * (D * δ) + ‖c‖ * (C * (D * δ)) := by
      rw [norm_mul]
      exact add_le_add h₂ (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
    _ = (C * D * (1 + ‖c‖)) * δ := by ring
    _ ≤ ε := hδ

end Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerEquivariance
