import Langlands.Global.RankinSelberg.RealSmoothRowCharacterAbsorption
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof

/-! # Schwartz row multiplication on real smooth Whittaker coefficients -/

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.RealSmoothRowAbsorption

open Langlands.Archimedean Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (appendIdentity appendIdentity_mul_zeroRowColumnUnipotent lastRow
  zeroRowColumnEntries zeroRowColumnUnipotent zeroRowColumnUnipotent_mem_upperUnipotent
  zeroRowColumnUnipotent_superdiagonal_sum continuous_zeroRowColumnUnipotent)
open ArchimedeanLocal DerivativeSmoothVectors

universe u

variable {r d : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "n" => r + (d + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "X" => (Fin (r + 1) → ℝ)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation:max "D" R:max => DerivativeSmoothVectors I R
local notation "j" => zeroRowColumnUnipotent (F := ℝ) r d

private def columnCLM : X →L[ℝ] Mat :=
  ({ toFun := zeroRowColumnEntries r d
     map_add' x y := by
       ext i k
       by_cases hi : i.val < r + 1 <;> by_cases hk : k.val = r + 1 <;>
         simp only [zeroRowColumnEntries, hi, hk, ↓reduceDIte, ↓reduceIte, Matrix.add_apply,
           Pi.add_apply, add_zero]
     map_smul' c x := by
       ext i k
       by_cases hi : i.val < r + 1 <;> by_cases hk : k.val = r + 1 <;>
         simp only [zeroRowColumnEntries, hi, hk, ↓reduceDIte, ↓reduceIte, Matrix.smul_apply,
           Pi.smul_apply, RingHom.id_apply, smul_zero] } : X →ₗ[ℝ] Mat).toContinuousLinearMap

private theorem unitHeight_column_le (x : X) :
    unitHeight (j x) ≤ (1 + ‖(1 : Mat)‖ + ‖columnCLM (r := r) (d := d)‖) * max 1 ‖x‖ := by
  let c := columnCLM (r := r) (d := d)
  let C : ℝ := 1 + ‖(1 : Mat)‖ + ‖c‖
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith only [norm_nonneg (1 : Mat), norm_nonneg c]
  have hx : 1 ≤ max 1 ‖x‖ := le_max_left _ _
  have hc := c.le_opNorm x
  change ‖zeroRowColumnEntries r d x‖ ≤ ‖c‖ * ‖x‖ at hc
  have hbound : ‖(1 : Mat)‖ + ‖zeroRowColumnEntries r d x‖ ≤ C * max 1 ‖x‖ := by
    calc
      _ ≤ ‖(1 : Mat)‖ * max 1 ‖x‖ + ‖c‖ * max 1 ‖x‖ :=
        add_le_add (le_mul_of_one_le_right (norm_nonneg _) hx)
          (hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)))
      _ ≤ C * max 1 ‖x‖ := by
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hx)
        dsimp [C]
        linarith
  apply max_le
  · exact (hC.trans (le_mul_of_one_le_right (by positivity : 0 ≤ C) hx))
  apply max_le
  · exact (norm_add_le _ _).trans hbound
  · exact (norm_sub_le _ _).trans hbound

/-- The column unipotents and their inverses grow at most linearly in the column. -/
theorem exists_columnHeightBound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : X,
    unitHeight (j x) ≤ K * max 1 ‖x‖ :=
  ⟨1 + ‖(1 : Mat)‖ + ‖columnCLM (r := r) (d := d)‖, by positivity, unitHeight_column_le⟩

/-- Multiplying a real smooth Whittaker coefficient by a Schwartz function of
its leading-block last row is realized by a single smooth vector. -/
def RealSmoothRowAbsorptionStatement : Prop :=
  ∀ (r d : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Langlands.GeneralLinear (r + (d + 1) + 1) ℝ →* (E →L[ℂ] E)),
    let model := matrixModel ℝ (r + (d + 1) + 1)
    let V := DerivativeSmoothVectors model R
    IsContinuousRepresentation R →
    ∀ (a : ℝˣ) (L : V →L[ℂ] ℂ),
      (∀ (u : Langlands.GeneralLinear.upperUnipotent (r + (d + 1) + 1) ℝ) (v : V),
        L (representation model R u.val v) = realWhittakerCharacter a u.val * L v) →
      ∀ (v : V) (Φ : 𝓢((Fin (r + 1) → ℝ), ℂ)), ∃ w : V,
        ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
          L (representation model R (appendIdentity r (d + 1) g) w) =
            L (representation model R (appendIdentity r (d + 1) g) v) * Φ (lastRow g)

theorem realSmoothRowAbsorption : RealSmoothRowAbsorptionStatement.{u} := by
  intro r d E _ _ _ R model V hR a L hL v Φ
  let column := zeroRowColumnUnipotent (F := ℝ) r d
  obtain ⟨C, k, hC, hNorm⟩ := exists_norm_le_unitHeight_pow ℝ (r + (d + 1) + 1) R hR
  refine RealSmoothRowCharacterAbsorption.realSmoothRowCharacterAbsorption R hR (r + 1) a column
    (continuous_zeroRowColumnUnipotent r d) (exists_columnHeightBound (r := r) (d := d))
    ⟨C, k, hC, fun x => hNorm (column x)⟩ L (appendIdentity r (d + 1)) lastRow ?_ v Φ
  intro g x w
  rw [← Module.End.mul_apply, ← map_mul, appendIdentity_mul_zeroRowColumnUnipotent,
    map_mul, Module.End.mul_apply]
  let z := g.val *ᵥ x
  let u : Langlands.GeneralLinear.upperUnipotent (r + (d + 1) + 1) ℝ :=
    ⟨column z, zeroRowColumnUnipotent_mem_upperUnipotent r d z⟩
  change L (representation model R u.val (representation model R (appendIdentity r (d + 1) g) w)) = _
  rw [hL, realWhittakerCharacter, show u.val = zeroRowColumnUnipotent r d z from rfl,
    zeroRowColumnUnipotent_superdiagonal_sum]
  have hz : z (Fin.last r) = ∑ i, x i * lastRow g i := by
    change (∑ i : Fin (r + 1), g.val (Fin.last r) i * x i) = _
    exact Finset.sum_congr rfl fun i _ => mul_comm (g.val (Fin.last r) i) (x i)
  rw [hz]

end Langlands.Global.RankinSelbergGlobal.RealSmoothRowAbsorption
