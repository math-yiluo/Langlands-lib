import Langlands.Global.RankinSelberg.ComplexLocalIwasawa
import Langlands.Global.RankinSelberg.ComplexLocalUnequalKernels
import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Representation.Archimedean.TransposePairingRestriction

/-! # The simple-root estimate for Weyl inverse-transpose Whittaker functions -/

noncomputable section
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace ComplexLocalDualWhittakerGauge

open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)
open RealEqualDualConvergence (revNeg rootPos_revNeg sum_abs_revNeg)
open RealConvergenceAnalysis (rootPos)
open Langlands.GeneralLinear (inverseTranspose weylLong)

theorem weylLong_mem_unitary (n : ℕ) : weylLong n ℂ ∈ unitaryCompact ℂ n := by
  change (weylLong n ℂ).val ∈ Matrix.unitaryGroup (Fin n) ℂ
  have hstar : star (weylLong n ℂ).val = (weylLong n ℂ).val.transpose := by
    ext i j
    change star (weylLong n ℂ j i) = weylLong n ℂ j i
    rw [GeneralLinear.weylLong_entry]
    split_ifs <;> simp
  have ht := congrArg Units.val (GeneralLinear.inverseTranspose_weylLong n ℂ)
  rw [GeneralLinear.inverseTranspose_coe, GeneralLinear.weylLong_inv] at ht
  rw [Matrix.mem_unitaryGroup_iff, hstar, ht, ← Units.val_mul,
    GeneralLinear.weylLong_mul_self, Units.val_one]

theorem inverseTranspose_mem_unitary {n : ℕ} (k : unitaryCompact ℂ n) :
    inverseTranspose n ℂ k.val ∈ unitaryCompact ℂ n := by
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨k.val.val, k.2⟩
  have hu : Unitary.toUnits u = k.val := Units.ext rfl
  rw [← hu, inverseTranspose_unitaryToUnits]
  exact (compactIota ℂ n u).2

private theorem inverseTranspose_logTorus {n : ℕ} (y : Fin n → ℝ) :
    inverseTranspose n ℂ (logTorus y) = logTorus (-y) := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, logTorus_inv_val, Matrix.diagonal_transpose, logTorus_val]
  rfl

private theorem weylLong_logTorus_weylLong {n : ℕ} (y : Fin n → ℝ) :
    weylLong n ℂ * logTorus y * weylLong n ℂ = logTorus (fun i => y i.rev) := by
  apply Units.ext
  ext i j
  rw [GeneralLinear.weylLong_conjugate_entry]
  simp only [logTorus_val, Matrix.diagonal_apply, Fin.rev_inj]

private def dualUnitary {n : ℕ} (k : unitaryCompact ℂ n) : unitaryCompact ℂ n :=
  ⟨weylLong n ℂ * inverseTranspose n ℂ k.val,
    mul_mem (weylLong_mem_unitary n) (inverseTranspose_mem_unitary k)⟩

private theorem dual_logTorus_mul {r : ℕ}
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (y : Fin (r + 1) → ℝ)
    (k : unitaryCompact ℂ (r + 1)) :
    ArchimedeanLocal.dualFunction (r + 1) W (logTorus y * k.val) =
      W (logTorus (revNeg y) * (dualUnitary k).val) := by
  unfold ArchimedeanLocal.dualFunction
  congr 1
  rw [map_mul, inverseTranspose_logTorus]
  have h : logTorus (revNeg y) =
      weylLong (r + 1) ℂ * logTorus (-y) * (weylLong (r + 1) ℂ)⁻¹ := by
    rw [GeneralLinear.weylLong_inv, weylLong_logTorus_weylLong]
    rfl
  rw [h]
  change _ = _ * (weylLong (r + 1) ℂ * inverseTranspose (r + 1) ℂ k.val)
  group

theorem exists_gauge {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
      ‖ArchimedeanLocal.dualFunction (r + 1) W.val g‖ ≤
        C * Real.exp ((N : ℝ) * (∑ j, |alpha g j|) - (M : ℝ) * rootPos (alpha g)) := by
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization r ds a W
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M []
  refine ⟨C, hC, fun g => ?_⟩
  have h := complexWhittakerModel_dual_left_mul W.2 (npart g) (logTorus (alpha g) * (kpart g).val)
  rw [← mul_assoc, npart_mul_logTorus_mul_kpart] at h
  rw [h, norm_mul]
  simp only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
    one_mul, dual_logTorus_mul]
  have hb' := hb (revNeg (alpha g)) (dualUnitary (kpart g))
  change ‖W.val (logTorus (revNeg (alpha g)) * (dualUnitary (kpart g)).val)‖ ≤
    C * Real.exp ((N : ℝ) * (∑ j, |revNeg (alpha g) j|) -
      (M : ℝ) * rootPos (revNeg (alpha g))) at hb'
  rwa [sum_abs_revNeg, rootPos_revNeg] at hb'

end ComplexLocalDualWhittakerGauge

/-- The dual coefficient has arbitrary positive simple-root decay and fixed toral growth on the
complex matrix group. -/
def ComplexDualWhittakerGaugeStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds a),
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
      ‖ArchimedeanLocal.dualFunction (r + 1) W.val g‖ ≤ C * Real.exp
        ((N : ℝ) * (∑ j, |ComplexLocalIwasawa.alpha g j|) -
          (M : ℝ) * RealConvergenceAnalysis.rootPos (ComplexLocalIwasawa.alpha g))

theorem complexDualWhittakerGauge : ComplexDualWhittakerGaugeStatement :=
  fun _ _ _ W => ComplexLocalDualWhittakerGauge.exists_gauge W

end Langlands.Global.RankinSelbergGlobal
