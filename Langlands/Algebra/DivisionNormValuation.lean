import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Valuation.Basic

/-! A valuation on a finite-dimensional division algebra from the regular norm. -/

noncomputable section

namespace Langlands.CentralDivision

universe uK uD uL

section FieldNorm

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] {L : Type uL} [Field L] [Algebra K L]
  [FiniteDimensional K L]

theorem norm_fieldNorm_powerBasis_gen (pb : PowerBasis K L) :
    ‖Algebra.norm K pb.gen‖ = spectralNorm K L pb.gen ^ Module.finrank K L := by
  have hn : ((minpoly K pb.gen).natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (minpoly.natDegree_pos pb.isIntegral_gen).ne'
  have h := (Real.eq_rpow_inv (spectralNorm_nonneg pb.gen)
    (norm_nonneg ((minpoly K pb.gen).coeff 0)) hn).mp
      (by simpa only [one_div] using
        spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L pb.gen)
  rw [Real.rpow_natCast] at h
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, pb.finrank, ← pb.natDegree_minpoly]
  exact h.symm

/-- The norm of the field norm is the degree-th power of the spectral norm. -/
theorem norm_fieldNorm_eq_spectralNorm_pow (x : L) :
    ‖Algebra.norm K x‖ = spectralNorm K L x ^ Module.finrank K L := by
  let pb := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := K) x)
  rw [Algebra.norm_eq_norm_adjoin K x, norm_pow]
  change ‖Algebra.norm K pb.gen‖ ^ _ = _
  rw [norm_fieldNorm_powerBasis_gen pb, ← pow_mul, Module.finrank_mul_finrank,
    spectralNorm.eq_of_tower (K := K) (L := L) pb.gen]
  rfl

/-- Composing the field norm with the base norm gives an ultrametric function. -/
theorem norm_fieldNorm_add_le (x y : L) :
    ‖Algebra.norm K (x + y)‖ ≤ max ‖Algebra.norm K x‖ ‖Algebra.norm K y‖ := by
  simp only [norm_fieldNorm_eq_spectralNorm_pow]
  apply (pow_le_pow_left₀ (spectralNorm_nonneg _)
    (isNonarchimedean_spectralNorm x y) _).trans_eq
  simpa only [Real.rpow_natCast] using Real.rpow_max
    (spectralNorm_nonneg x) (spectralNorm_nonneg y)
    (Nat.cast_nonneg (Module.finrank K L) : (0 : ℝ) ≤ _)

end FieldNorm

section Restriction

variable {K : Type uK} [Field K] {D : Type uD} [DivisionRing D]
  [Algebra K D] [FiniteDimensional K D]
  {L : Type uL} [Field L] [Algebra K L]

/-- The regular norm on an embedded field is a power of its actual field norm. -/
theorem regularNorm_map_field (ι : L →ₐ[K] D) (a : L) :
    Algebra.norm K (ι a) =
      let : Module L D := Module.compHom D ι.toRingHom
      Algebra.norm K a ^ Module.finrank L D := by
  let : Module L D := Module.compHom D ι.toRingHom
  let : IsScalarTower K L D := ⟨fun k l x => by
    change ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩
  let : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite K L D
  have hm : (a • (LinearMap.id : D →ₗ[L] D)).restrictScalars K =
      Algebra.lmul K D (ι a) := by
    ext x
    rfl
  rw [Algebra.norm_apply, ← hm, LinearMap.det_restrictScalars]
  simp [LinearMap.det_smul]

end Restriction

section Normed

variable (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] (D : Type uD) [DivisionRing D]
  [Algebra K D] [FiniteDimensional K D]

theorem norm_regularNorm_one_add_le (z : D) :
    ‖Algebra.norm K (1 + z)‖ ≤ max 1 ‖Algebra.norm K z‖ := by
  let E := Algebra.adjoin K ({z} : Set D)
  let : Field E := fieldOfFiniteDimensional K E
  let ι : E →ₐ[K] D := (Algebra.adjoin K ({z} : Set D)).val
  let a : E := ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩
  have h := norm_fieldNorm_add_le (K := K) (1 : E) a
  simp only [map_one, norm_one] at h
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h
    (@Module.finrank E D _ _ (Module.compHom D ι.toRingHom))
  have hmax : (max (1 : ℝ) ‖Algebra.norm K a‖) ^
      (@Module.finrank E D _ _ (Module.compHom D ι.toRingHom)) =
      max 1 (‖Algebra.norm K a‖ ^
        (@Module.finrank E D _ _ (Module.compHom D ι.toRingHom))) := by
    simpa only [Real.rpow_natCast, one_pow] using Real.rpow_max
      (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (Algebra.norm K a))
      (Nat.cast_nonneg (@Module.finrank E D _ _ (Module.compHom D ι.toRingHom)) :
        (0 : ℝ) ≤ _)
  rw [hmax] at hpow
  change ‖Algebra.norm K (ι (1 + a))‖ ≤ max 1 ‖Algebra.norm K (ι a)‖
  rw [regularNorm_map_field, regularNorm_map_field, norm_pow, norm_pow]
  exact hpow

/-- The regular algebra norm composed with the base norm is ultrametric on the division algebra. -/
theorem norm_regularNorm_add_le (x y : D) :
    ‖Algebra.norm K (x + y)‖ ≤ max ‖Algebra.norm K x‖ ‖Algebra.norm K y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : Algebra.norm K x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h := mul_le_mul_of_nonneg_left
    (norm_regularNorm_one_add_le K D (x⁻¹ * y)) (norm_nonneg (Algebra.norm K x))
  have heq : x * (1 + x⁻¹ * y) = x + y := by
    simp [mul_add, hx]
  calc
    ‖Algebra.norm K (x + y)‖ =
        ‖Algebra.norm K x‖ * ‖Algebra.norm K (1 + x⁻¹ * y)‖ := by
      rw [← norm_mul, ← map_mul, heq]
    _ ≤ ‖Algebra.norm K x‖ * max 1 ‖Algebra.norm K (x⁻¹ * y)‖ := h
    _ = max ‖Algebra.norm K x‖ ‖Algebra.norm K y‖ := by
      rw [mul_max_of_nonneg _ _ (norm_nonneg _), mul_one]
      congr 1
      rw [map_mul, Algebra.norm_inv, norm_mul, norm_inv, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_mul]

/-- An actual valuation on the original division algebra, with regular determinant normalization. -/
def regularNormValuation : Valuation D NNReal where
  toFun x := ‖Algebra.norm K x‖₊
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp
  map_add_le_max' x y := by
    exact_mod_cast norm_regularNorm_add_le K D x y

@[simp]
theorem regularNormValuation_algebraMap (a : K) :
    regularNormValuation K D (algebraMap K D a) = ‖a‖₊ ^ Module.finrank K D := by
  simp [regularNormValuation, Algebra.norm_algebraMap]

end Normed

end Langlands.CentralDivision
