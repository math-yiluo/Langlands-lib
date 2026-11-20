import Langlands.Global.RankinSelberg.ComplexGodementDiagonal
import Langlands.LocalFactor.ArchimedeanGamma
import Langlands.LocalFactor.ArchimedeanPairFactor

/-! # The Tate exponents of the triangular Godement integral -/

noncomputable section

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_ne_zero)

set_option autoImplicit false

private theorem positionCharacter_ofFn : ∀ {n : ℕ} (es : Fin n → ComplexCharacterData)
    (j : Fin n) (z : ℂˣ), complexPositionCharacter (List.ofFn es) j z = ((es j).character z : ℂ)
  | 0, _, j, _ => j.elim0
  | n + 1, es, j, z => by
    rw [List.ofFn_succ]
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact positionCharacter_ofFn (fun i : Fin n => es i.succ) j z

private theorem characterQuotient_eq (d e : ComplexCharacterData) (z : ℂˣ) :
    (d.character z : ℂ) * (e.character z⁻¹ : ℂ) =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (d.weight - e.weight) *
        (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent - e.exponent)) := by
  have h : (d.character z : ℂ) * (e.character z⁻¹ : ℂ) = ((d.mul e.inverse).character z : ℂ) := by
    rw [map_inv]
    rfl
  rw [h, (d.mul e.inverse).character_eq]
  change _ ^ (d.weight + -e.weight) * _ ^ (2 * (d.exponent + -e.exponent)) = _
  rw [sub_eq_add_neg, sub_eq_add_neg]

/-- Relative to complex additive Lebesgue measure, the diagonal Godement weight has the Tate
angular weight `d.weight - e.weight` and spectral exponent `d.exponent - e.exponent + 1` in
that position. The inverse squared norm densities account for the `−2` in Tate's radial power. -/
theorem diagonalTateWeight_mul_density {n : ℕ} (d : ComplexCharacterData)
    (es : Fin n → ComplexCharacterData) (a : Fin n → ℂˣ) :
    (∏ j : Fin n, (((‖(a j : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ)) * diagonalTateWeight d (List.ofFn es) a =
      ∏ j : Fin n, ((a j : ℂ) / (‖(a j : ℂ)‖ : ℂ)) ^ (d.weight - (es j).weight) *
        (‖(a j : ℂ)‖ : ℂ) ^ (2 * (d.exponent - (es j).exponent + 1) - 2) := by
  rw [diagonalTateWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [positionCharacter_ofFn]
  let z := a j
  let e := es j
  have hnum : 2 * (d.exponent - e.exponent + 1) - 2 = 2 * (d.exponent - e.exponent) := by ring
  change (((‖(z : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (((d.character z : ℂ) * (e.character z⁻¹ : ℂ)) * normPower 1 z) =
    ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (d.weight - e.weight) *
      (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent - e.exponent + 1) - 2)
  rw [hnum, ← characterQuotient_eq]
  change (((‖(z : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (((d.character z : ℂ) * (e.character z⁻¹ : ℂ)) * normSqC (z : ℂ) ^ (1 : ℂ)) = _
  rw [Complex.cpow_one, Complex.ofReal_inv]
  change (normSqC (z : ℂ))⁻¹ * (_ * normSqC (z : ℂ)) = _
  rw [mul_left_comm, inv_mul_cancel₀ (normSqC_ne_zero z.ne_zero), mul_one]

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
