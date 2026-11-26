import Langlands.Global.AdelicFiniteTranslateHeightReduction

/-! # Rational representatives with control of full adelic height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "H" => adelicHeight F G rho

/-- Every rational left orbit has a representative in a fixed compact set of
finite components whose full adelic height grows at most polynomially in
that of the given point. -/
def AdelicFullHeightRationalReductionStatement : Prop :=
  IsConnectedReductive G → IsClosedSubgroup rho → 0 < N →
  ∃ (K : Set (FiniteAdelicGroupPoints F G)) (B : ℝ) (m : ℕ), IsCompact K ∧ 1 ≤ B ∧
    ∀ g : A, ∃ q : RationalGroupPoints F G,
      finite F G (rational F G q * g) ∈ K ∧ H (rational F G q * g) ≤ B * H g ^ m

theorem adelicFullHeightRationalReduction : AdelicFullHeightRationalReductionStatement rho := by
  intro hG hrho hN
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨T, i, ν, T₀, j, hS, C, t, W, hW, hcover⟩ := hasFiniteRightSiegelCover_of_connectedReductive F G hG
  obtain ⟨b, d, hmin⟩ := siegelNormMinimalityStatement F G rho hG hrho hN T i ν T₀ j hS C t
  obtain ⟨a, e, hcentral⟩ := centralNormOneHeightFactorStatement F G rho hG hrho hN
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨K, hK, hKfin⟩ := exists_isCompact_finite_weakSiegelProduct F G T i ν T₀ j hT₀
    (canonicalStandardFactors F G T i ν) C t
  obtain ⟨c, hc⟩ := (hW.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  let B := max 1 a * max 1 c
  let M := max 1 b
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hM : 1 ≤ M := le_max_left _ _
  have hH (x : A) : 0 ≤ H x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  have hW' (w : A) (hw : w ∈ W) : H w ≤ max 1 c := (hc ⟨w, hw, rfl⟩).trans (le_max_right _ _)
  refine ⟨K * (finite F G '' W), M * B ^ (d + 1), (e + 1) * (d + 1),
    hK.mul (hW.isCompact.image (finite F G).continuous),
    one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hB), fun g => ?_⟩
  obtain ⟨z, hzcentral, hzfinite, hzOne, hzHeight⟩ := hcentral g
  obtain ⟨q, s, hs, w, hw, hsw⟩ := hcover ⟨z⁻¹ * g, hzOne⟩
  have hq : rational F G q * (z⁻¹ * g) = s * w := hsw.symm
  have hqg : rational F G q * g = z * s * w := by
    calc
      _ = z * (rational F G q * (z⁻¹ * g)) := by
        rw [← mul_assoc, (hzcentral _).eq, mul_assoc, mul_inv_cancel_left]
      _ = _ := by rw [hq, mul_assoc]
  refine ⟨q, ?_, ?_⟩
  · rw [hqg, map_mul, map_mul, hzfinite, one_mul]
    exact Set.mul_mem_mul (hKfin s hs) (mem_image_of_mem _ hw)
  have hpre : rational F G q⁻¹ * s = z⁻¹ * g * w⁻¹ := by
    rw [← mul_inv_cancel_right s w, ← hq, map_inv]
    group
  have hz : H z ≤ max 1 a * H g ^ e :=
    hzHeight.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hH _) _))
  have hmul (x y : A) : H (x * y) ≤ H x * H y := adelicHeight_mul_le F G rho hN x y
  have hpreHeight : H (rational F G q⁻¹ * s) ≤ B * H g ^ (e + 1) := by
    rw [hpre]
    calc
      _ ≤ (H z⁻¹ * H g) * H w⁻¹ := (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (hH _))
      _ ≤ (max 1 a * H g ^ e * H g) * max 1 c := by
        rw [adelicHeight_inv, adelicHeight_inv]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (hH _)) (hW' w hw)
          (hH _) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (hH _) _)) (hH _))
      _ = _ := by rw [pow_succ]; unfold B; ring
  have hsHeight : H s ≤ M * (B * H g ^ (e + 1)) ^ d := by
    calc
      _ ≤ b * H (rational F G q⁻¹ * s) ^ d := hmin s hs q⁻¹
      _ ≤ M * H (rational F G q⁻¹ * s) ^ d :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hH _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH _) hpreHeight _) (zero_le_one.trans hM)
  rw [hqg]
  calc
    H (z * s * w) ≤ H z * H s * H w := (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (hH _))
    _ ≤ (max 1 a * H g ^ e) * (M * (B * H g ^ (e + 1)) ^ d) * max 1 c := by
      have hZ₀ : 0 ≤ max 1 a * H g ^ e := mul_nonneg (by positivity) (pow_nonneg (hH g) _)
      have hS₀ : 0 ≤ M * (B * H g ^ (e + 1)) ^ d :=
        mul_nonneg (zero_le_one.trans hM)
          (pow_nonneg (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (hH g) _)) _)
      exact mul_le_mul (mul_le_mul hz hsHeight (hH s) hZ₀) (hW' w hw) (hH w) (mul_nonneg hZ₀ hS₀)
    _ = M * (B * H g ^ (e + 1)) ^ d * B * H g ^ e := by unfold B; ring
    _ ≤ M * (B * H g ^ (e + 1)) ^ d * B * H g ^ (e + 1) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (one_le_adelicHeight F G rho hN g) (Nat.le_succ e))
        (mul_nonneg (mul_nonneg (zero_le_one.trans hM)
          (pow_nonneg (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (hH g) _)) _))
          (zero_le_one.trans hB))
    _ = M * B ^ (d + 1) * H g ^ ((e + 1) * (d + 1)) := by
      rw [pow_mul (H g), mul_pow, pow_succ B d, pow_succ (H g ^ (e + 1)) d]
      ring

end Langlands.Global.RepresentationGrowth
