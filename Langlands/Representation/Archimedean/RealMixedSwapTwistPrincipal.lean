import Langlands.Representation.Archimedean.RealMixedSwapTwist

/-!
# Principal-series transport by signed real reversal
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem wMat_conj_apply (M : A) (i j : Fin 3) :
    (wMat * M * wMat) i j =
      (if i = 1 then -1 else 1) * (if j = 1 then -1 else 1) *
        M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.rev]

theorem w_conj_diagonal (a : Fin 3 → ℝˣ) :
    w * theta (Iwasawa.diagonalUnits a : G) * w =
      Iwasawa.diagonalUnits (fun i => (a (Fin.rev i))⁻¹) := by
  apply Units.ext
  change wMat * (((Iwasawa.diagonalUnits a : G)⁻¹ : G) : A)ᵀ * wMat = _
  rw [← map_inv, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val,
    Matrix.diagonal_transpose]
  ext i j
  rw [wMat_conj_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    split_ifs <;> ring
  · rw [ite_eq_right (fun h => hij (Fin.rev_injective h)), ite_eq_right hij, mul_zero]

theorem w_conj_upperUnipotent (u : upperUnipotent 3 ℝ) :
    w * theta (u : G) * w ∈ upperUnipotent 3 ℝ := by
  have hv := (u⁻¹ : upperUnipotent 3 ℝ).2
  have hval : ((w * theta (u : G) * w : G) : A) =
      wMat * (((u⁻¹ : upperUnipotent 3 ℝ) : G) : A)ᵀ * wMat := rfl
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change ((w * theta (u : G) * w : G) : A) i j = 0
    rw [hval, wMat_conj_apply, Matrix.transpose_apply]
    have hz :
        (((u⁻¹ : upperUnipotent 3 ℝ) : G) : A) (Fin.rev j) (Fin.rev i) = 0 :=
      hv.1 (Fin.rev_lt_rev.mpr hij)
    exact mul_eq_zero_of_right _ hz
  · change ((w * theta (u : G) * w : G) : A) i i = 1
    rw [hval, wMat_conj_apply, Matrix.transpose_apply, hv.2 (Fin.rev i)]
    split_ifs <;> norm_num

theorem twist_diagonal_mul (a : Fin 3 → ℝˣ) (u : upperUnipotent 3 ℝ) (g : G) :
    twist ((Iwasawa.diagonalUnits a : G) * (u : G) * g) =
      (Iwasawa.diagonalUnits (fun i => (a (Fin.rev i))⁻¹) : G) *
        ((⟨_, w_conj_upperUnipotent u⟩ : upperUnipotent 3 ℝ) : G) * twist g := by
  rw [← w_conj_diagonal]
  change w * theta (_ * _ * g) = _ * (w * theta (u : G) * w) * (w * theta g)
  simp only [map_mul, mul_assoc, ← mul_assoc w w, w_mul_self, one_mul]

/-- Invert and reverse the first three inducing characters. -/
def reverseCharacters (χ : ℕ → ℝˣ → ℂ) (p : ℕ) (x : ℝˣ) : ℂ :=
  χ (2 - p) x⁻¹

theorem norm_inv_cpow (x : ℝˣ) (c : ℂ) :
    (‖((x⁻¹ : ℝˣ) : ℝ)‖ : ℂ) ^ (-c) = (‖(x : ℝ)‖ : ℂ) ^ c := by
  rw [Units.val_inv_eq_inv_val, norm_inv, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
      exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv]

theorem principalSeriesCharacter_rev_inv {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = χ (Fin.rev j) x⁻¹)
    (a : Fin 3 → ℝˣ) :
    principalSeriesCharacter ℝ 3 χ (fun i => (a (Fin.rev i))⁻¹) =
      principalSeriesCharacter ℝ 3 χ' a := by
  unfold principalSeriesCharacter
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Module.finrank_self, pow_one]
  rw [hχ' j]
  congr 1
  norm_num only [Nat.cast_ofNat]
  have hrev : (((Fin.rev j : Fin 3) : ℕ) : ℂ) = 3 - 1 - (j : ℕ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    norm_num
    ring
  rw [hrev, show (1 : ℂ) - (3 - 1 - ((j : ℕ) : ℂ)) =
      -(1 - ((j : ℕ) : ℂ)) by ring, norm_inv_cpow]

/-- Pullback along signed reversal inverts and reverses the principal-series characters. -/
theorem twistLin_mem_principalSeries {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = χ (Fin.rev j) x⁻¹)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ 3 χ) :
    twistLin f ∈ principalSeries ℝ 3 χ' := by
  refine ⟨contMDiff_twistLin hf.1, fun a u g => ?_⟩
  rw [twistLin_apply, twistLin_apply, twist_diagonal_mul, hf.2,
    principalSeriesCharacter_rev_inv hχ']

/-- The principal-series transport also preserves orthogonal finiteness. -/
theorem twistLin_mem_kFiniteFunctions {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = χ (Fin.rev j) x⁻¹)
    {f : G → ℂ} (hf : f ∈ kFiniteFunctions (principalSeries ℝ 3 χ) (unitaryCompact ℝ 3)) :
    twistLin f ∈ kFiniteFunctions (principalSeries ℝ 3 χ') (unitaryCompact ℝ 3) :=
  ⟨twistLin_mem_principalSeries hχ' hf.1, twistLin_mem_kFiniteVectors hf.2⟩

end Langlands.Archimedean.RealMixedSwapTwist
