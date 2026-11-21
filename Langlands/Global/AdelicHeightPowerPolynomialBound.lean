import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Polynomial adelic bounds for fixed Iwasawa height powers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {P : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

private theorem parameterPower_le_height (rho : MatrixRepresentation P (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) (lam : ComplexCharacterParameter F P) :
    ∃ C d : ℝ, 0 < C ∧ 0 ≤ d ∧ ∀ x : AdelicGroupPoints F P,
      ‖parameterPower F P lam x‖ ≤ C * adelicHeight F P rho x ^ d := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    obtain ⟨C, hC, e, hb⟩ := exists_characterNorm_le F rho hN hrho χ
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    let d := |s.re|
    refine ⟨C ^ d, (e : ℝ) * d, Real.rpow_pos_of_pos hCpos _, by positivity, fun x => ?_⟩
    let H := adelicHeight F P rho x
    let t : ℝ := ((characterNorm F P χ.toMul x : ℝ≥0) : ℝ)
    have hH : 0 < H := zero_lt_one.trans_le (one_le_adelicHeight F P rho hN x)
    have ht : 0 < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (characterNorm F P χ.toMul x).ne_zero)
    have hz : t ≤ C * H ^ e := (hb x).1
    have hzi : t⁻¹ ≤ C * H ^ e := by
      simpa only [t, Units.val_inv_eq_inv_val, NNReal.coe_inv] using (hb x).2
    have hlog₁ := Real.log_le_log ht hz
    have hlog₂ := Real.log_le_log (inv_pos.mpr ht) hzi
    rw [Real.log_inv] at hlog₂
    have hlog : |Real.log t| ≤ Real.log (C * H ^ e) := abs_le.mpr ⟨by linarith, hlog₁⟩
    have he : s.re * Real.log t ≤ d * Real.log (C * H ^ e) := calc
      _ ≤ |s.re * Real.log t| := le_abs_self _
      _ = d * |Real.log t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    calc
      ‖parameterPower F P (s ⊗ₜ[ℤ] χ) x‖ = Real.exp (s.re * Real.log t) := by
        rw [parameterPower, Complex.norm_exp, complexParameterPairing_tmul,
          characterLog_apply, Complex.mul_re]
        simp [t]
      _ ≤ Real.exp (d * Real.log (C * H ^ e)) := Real.exp_le_exp.mpr he
      _ = C ^ d * H ^ ((e : ℝ) * d) := by
        rw [Real.log_mul hCpos.ne' (pow_pos hH _).ne', Real.log_pow, mul_add, Real.exp_add,
          Real.rpow_def_of_pos hCpos, Real.rpow_def_of_pos hH]
        congr 1 <;> congr 1 <;> ring
  | add lam eta hlam heta =>
    obtain ⟨A, d, hA, hd, hbA⟩ := hlam
    obtain ⟨B, e, hB, he, hbB⟩ := heta
    refine ⟨A * B, d + e, mul_pos hA hB, add_nonneg hd he, fun x => ?_⟩
    simp only [parameterPower, map_add, LinearMap.add_apply, Complex.exp_add, norm_mul]
    calc
      _ ≤ (A * adelicHeight F P rho x ^ d) * (B * adelicHeight F P rho x ^ e) :=
        mul_le_mul (hbA x) (hbB x) (norm_nonneg _)
          (mul_nonneg hA.le (Real.rpow_nonneg ((one_le_adelicHeight F P rho hN x).trans'
            (zero_le_one : 0 ≤ (1 : ℝ))) _))
      _ = _ := by
        rw [Real.rpow_add (zero_lt_one.trans_le (one_le_adelicHeight F P rho hN x))]
        ring

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- A fixed parameter power of the actual Iwasawa height grows at most
polynomially in any positive-rank closed adelic matrix embedding. -/
theorem IsIwasawaCompact.exists_norm_heightPower_le_adelicHeight
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hrho : IsClosedSubgroup rho) (lam : ComplexCharacterParameter F P) :
    ∃ C d : ℝ, 0 < C ∧ 0 ≤ d ∧ ∀ g : AdelicGroupPoints F G,
      ‖hK.heightPower lam g‖ ≤ C * adelicHeight F G rho g ^ d := by
  obtain ⟨A, d, hA, hd, hbound⟩ :=
    parameterPower_le_height (p ≫ rho) hN
      (IsClosedSubgroup.comp (show IsClosedSubgroup p from inferInstanceAs
        (IsClosedImmersion p.hom.hom.left)) hrho) lam
  obtain ⟨B, hB⟩ := (hK.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  let C := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨A * C ^ d, d, mul_pos hA (Real.rpow_pos_of_pos hC _), hd, fun g => ?_⟩
  obtain ⟨y, k, hk, hy⟩ := hK.exists_eq g
  have hEq : map F P G p y = g * k⁻¹ := by rw [← hy, mul_inv_cancel_right]
  have hHeight : adelicHeight F P (p ≫ rho) y = adelicHeight F G rho (map F P G p y) := by
    change AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
      (map F P _ (p ≫ rho) y)) = AdelicMatrixHeight.height F N
        (GeneralLinearGroupPoints.adelicHomeomorph F N (map F G _ rho (map F P G p y)))
    rw [map_comp_apply_of_hom]
  have hkH : adelicHeight F G rho k⁻¹ ≤ C :=
    (hB ⟨k⁻¹, K.inv_mem hk, rfl⟩).trans (le_max_left _ _)
  have hH : 0 ≤ adelicHeight F G rho g :=
    zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hb : adelicHeight F P (p ≫ rho) y ≤ adelicHeight F G rho g * C := by
    rw [hHeight, hEq]
    exact (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_left hkH hH)
  rw [IsIwasawaCompact.heightPower, hK.height_eq hk hy, ← parameterPower]
  calc
    _ ≤ A * adelicHeight F P (p ≫ rho) y ^ d := hbound y
    _ ≤ A * (adelicHeight F G rho g * C) ^ d :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (zero_le_one.trans (one_le_adelicHeight F P (p ≫ rho) hN y)) hb hd) hA.le
    _ = _ := by rw [Real.mul_rpow hH hC.le]; ring

/-- A polynomial right-translation bound for the same fixed parameter,
uniform in the initial adelic argument. -/
def IwasawaHeightPowerPolynomialBoundStatement
    (rho : MatrixRepresentation G (Fin N)) (lam : ComplexCharacterParameter F P) : Prop :=
  ∃ C d : ℝ, 0 < C ∧ 0 ≤ d ∧ ∀ x g : AdelicGroupPoints F G,
    ‖hK.heightPower lam (x * g)‖ ≤
      C * adelicHeight F G rho g ^ d * ‖hK.heightPower lam x‖

theorem IsIwasawaCompact.iwasawaHeightPowerPolynomialBound
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hrho : IsClosedSubgroup rho) (lam : ComplexCharacterParameter F P) :
    IwasawaHeightPowerPolynomialBoundStatement hK rho lam := by
  obtain ⟨A, d, hA, hd, hbound⟩ := hK.exists_norm_heightPower_le_adelicHeight rho hN hrho lam
  obtain ⟨B, hB⟩ := (hK.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  let C := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨A * C ^ d, d, mul_pos hA (Real.rpow_pos_of_pos hC _), hd, fun x g => ?_⟩
  obtain ⟨k, hk, he⟩ := hK.exists_height_mul_eq_add x g
  have hkH : adelicHeight F G rho k ≤ C := (hB ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hgH : 0 ≤ adelicHeight F G rho g :=
    zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hmul : adelicHeight F G rho (k * g) ≤ C * adelicHeight F G rho g :=
    (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hkH hgH)
  have he' : hK.heightPower lam (x * g) = hK.heightPower lam x * hK.heightPower lam (k * g) := by
    simp only [IsIwasawaCompact.heightPower, he, map_add, Complex.exp_add]
  rw [he', norm_mul, mul_comm ‖hK.heightPower lam x‖]
  refine mul_le_mul_of_nonneg_right ((hbound _).trans ?_) (norm_nonneg _)
  calc
    _ ≤ A * (C * adelicHeight F G rho g) ^ d :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (zero_le_one.trans (one_le_adelicHeight F G rho hN (k * g))) hmul hd) hA.le
    _ = _ := by rw [Real.mul_rpow hC.le hgH, mul_assoc]

end Langlands.Global.AdelicGroupPoints
