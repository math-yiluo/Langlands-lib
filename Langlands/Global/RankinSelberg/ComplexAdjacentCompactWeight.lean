import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Global.RankinSelberg.ComplexSquareFourierUnitaryAverage
import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise

/-! # Paired compact weights for the adjacent-rank matrix tests -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap
open scoped Langlands.Archimedean.ComplexDuality

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist Langlands.GeneralLinear
open ComplexSquareFourier (matrixTransform complexSquareFourierUnitaryAverage)

set_option autoImplicit false

variable {r : ℕ}

local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ

/-- A single continuous compact weight reproduces both square tests of the adjacent
unfolding, with the inverse-transpose action on the Fourier-transformed test. -/
def ComplexAdjacentCompactWeightStatement : Prop :=
  ∀ (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (η : ℂˣ →* ℂˣ), Continuous η →
  ∀ (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))) →
    ∃ w : K → ℂ, Continuous w ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : K => fun k => w (h⁻¹ * k))) ∧
      (∀ X, ∫ k, w k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ k X ∂κ = Φ X) ∧
      (∀ X, ∫ k, w k * complexCompactMatrixTranslate η (matrixTransform a Φ)
        (conjK (r + 1) k) X ∂κ =
        matrixTransform a Φ X)

theorem complexAdjacentCompactWeight : ComplexAdjacentCompactWeightStatement (r := r) := by
  intro κ _ hκ η hη a Φ hΦ
  let ηd := η.comp invMonoidHom
  have hηd : Continuous ηd := hη.comp continuous_inv
  obtain ⟨w, hw, hwfin, hrec⟩ :=
    complexLocalCompactMatrixWeight (n := r + 1) κ hκ ηd hηd Φ Φ.continuous hΦ
  let w' (k : K) : ℂ := w k * (ηd (determinant k.val) : ℂ)
  have hw' : Continuous w' := hw.mul (Units.continuous_val.comp
    (hηd.comp (determinantContinuous.continuous.comp continuous_subtype_val)))
  have hmean (X : Mat) : Φ X =
      ∫ k : K, w' k * Φ ((k⁻¹ : K).val.val * X * (1 : K).val.val) ∂κ := by
    simpa only [w', complexCompactMatrixTranslate, Subgroup.coe_inv, Subgroup.coe_one,
      Units.val_one, Matrix.mul_one, mul_assoc] using (hrec X).symm
  refine ⟨w, hw, hwfin, hrec, fun X => ?_⟩
  have h := complexSquareFourierUnitaryAverage κ a w' (fun k : K => k⁻¹) (fun _ => (1 : K))
    hw' continuous_inv continuous_const Φ Φ hmean X
  have hdet (k : K) : determinant (conjK (r + 1) k).val = (determinant k.val)⁻¹ := by
    change determinant (inverseTranspose (r + 1) ℂ k.val) = _
    exact Langlands.RankinSelberg.HighlyRamified.determinant_inverseTranspose k.val
  simpa only [w', complexCompactMatrixTranslate, map_inv (conjK (r + 1)),
    map_one (conjK (r + 1)),
    Subgroup.coe_inv, Subgroup.coe_one, Units.val_one, Matrix.mul_one, hdet, ← mul_assoc,
    ηd, MonoidHom.comp_apply, invMonoidHom_apply] using h.symm

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
