import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicSiegelNormMinimalityProof
import Langlands.Global.AdelicCentralPositiveHeightProof

/-! # Rational height reduction from finitely many Siegel translates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Pointwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- A weak Siegel product covers the norm-one points up to rational left
translation and finitely many right translates. -/
def HasFiniteRightSiegelCover : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
    IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
      ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
        (t : ℝ≥0ˣ) (W : Set (AdelicGroupPoints F G)), W.Finite ∧
        ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
          rational F G q * (g : AdelicGroupPoints F G) ∈
            weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t * W

/-- The finite-volume covering construction gives this finite-translate
cover for every connected reductive group. -/
theorem hasFiniteRightSiegelCover_of_connectedReductive
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) :
    HasFiniteRightSiegelCover F G := by
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  obtain ⟨K, _, W, hKc, _, _, _, _, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hS
  obtain ⟨C, t, _, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hS K hKc W hW hW1 hcov
  exact ⟨T, i, ν, T₀, j, hS, C, t, W, hW, hcover⟩

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

/-- Finite right translates enlarge the compact set of finite coordinates.
Their heights and inverse heights contribute constant factors to norm
minimality on the unshifted Siegel product. -/
theorem adelicRationalHeightReduction_of_finiteRightSiegelCover :
    AdelicRationalHeightReductionStatement.{u} := by
  intro F _ _ G _ N rho hG hrho hN
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T, i, ν, T₀, j, hS, C, t, W, hW, hcover⟩ :=
    hasFiniteRightSiegelCover_of_connectedReductive F G hG
  obtain ⟨cm, em, hm⟩ := siegelNormMinimalityStatement F G rho hG hrho hN T i ν T₀ j hS C t
  obtain ⟨cz, ez, hz⟩ := centralNormOneHeightFactorStatement F G rho hG hrho hN
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨Ω, hΩ, hΩs⟩ := exists_isCompact_finite_weakSiegelProduct F G T i ν T₀ j hT₀
    (canonicalStandardFactors F G T i ν) C t
  let H := adelicHeight F G rho
  have hH (g : AdelicGroupPoints F G) : 0 ≤ H g :=
    zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  obtain ⟨cw, hcw⟩ := (hW.image H).bddAbove
  let M := max 1 cm
  let Z := max 1 cz
  let D := max 1 cw
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hZ : 0 < Z := zero_lt_one.trans_le (le_max_left _ _)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hw_le (w : AdelicGroupPoints F G) (hw : w ∈ W) : H w ≤ D :=
    (hcw ⟨w, hw, rfl⟩).trans (le_max_right _ _)
  refine ⟨Ω * (finite F G '' W), Z * M * (Z * D) ^ em * D, ez + (ez + 1) * em,
    hΩ.mul (hW.isCompact.image (finite F G).continuous),
    mul_pos (mul_pos (mul_pos hZ hM) (pow_pos (mul_pos hZ hD) em)) hD, fun g => ?_⟩
  obtain ⟨z, hzc, hzf, hz1, hzH⟩ := hz g
  obtain ⟨q, s, hs, w, hw, hsw⟩ := hcover ⟨z⁻¹ * g, hz1⟩
  have hqs : rational F G q * (z⁻¹ * g) = s * w := hsw.symm
  have hqg : rational F G q * g = z * s * w := by
    calc
      rational F G q * g = rational F G q * (z * (z⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = z * (rational F G q * (z⁻¹ * g)) := by rw [← mul_assoc, ← (hzc (rational F G q)).eq, mul_assoc]
      _ = z * s * w := by rw [hqs, mul_assoc]
  refine ⟨q, ?_, ?_⟩
  · rw [hqg, map_mul, map_mul, hzf, one_mul]
    exact ⟨_, hΩs s hs, _, ⟨w, hw, rfl⟩, rfl⟩
  have hsBack : rational F G q⁻¹ * s = z⁻¹ * g * w⁻¹ := by
    calc
      rational F G q⁻¹ * s = rational F G q⁻¹ * (s * w) * w⁻¹ := by group
      _ = z⁻¹ * g * w⁻¹ := by rw [← hqs, map_inv, inv_mul_cancel_left]
  have hZg : H z ≤ Z * H g ^ ez :=
    hzH.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hH _) _))
  have hDg : H w⁻¹ ≤ D := by
    change adelicHeight F G rho w⁻¹ ≤ _
    rw [adelicHeight_inv]
    exact hw_le w hw
  have hmul (x y : AdelicGroupPoints F G) : H (x * y) ≤ H x * H y :=
    adelicHeight_mul_le F G rho hN x y
  have hBack : H (rational F G q⁻¹ * s) ≤ (Z * D) * H g ^ (ez + 1) := by
    rw [hsBack]
    calc
      H (z⁻¹ * g * w⁻¹) ≤ H (z⁻¹ * g) * H w⁻¹ := hmul _ _
      _ ≤ (H z⁻¹ * H g) * H w⁻¹ := mul_le_mul_of_nonneg_right (hmul _ _) (hH _)
      _ ≤ (Z * H g ^ ez * H g) * D := by
        have hzinv : H z⁻¹ = H z := adelicHeight_inv F G rho z
        rw [hzinv]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hZg (hH g)) hDg (hH _)
          (mul_nonneg (mul_nonneg hZ.le (pow_nonneg (hH _) _)) (hH _))
      _ = (Z * D) * H g ^ (ez + 1) := by rw [pow_succ]; ring
  have hSg : H s ≤ M * ((Z * D) * H g ^ (ez + 1)) ^ em := by
    calc
      H s ≤ cm * H (rational F G q⁻¹ * s) ^ em := hm s hs q⁻¹
      _ ≤ M * H (rational F G q⁻¹ * s) ^ em :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hH _) _)
      _ ≤ M * ((Z * D) * H g ^ (ez + 1)) ^ em :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH _) hBack em) hM.le
  calc
    height F G rho (infinite F G (rational F G q * g)) ≤ H (rational F G q * g) :=
      height_infinite_le_adelicHeight F G rho hN _
    _ = H (z * s * w) := congrArg H hqg
    _ ≤ (H z * H s) * H w :=
      (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (hH _))
    _ ≤ (Z * H g ^ ez) * (M * ((Z * D) * H g ^ (ez + 1)) ^ em) * D := by
      exact mul_le_mul (mul_le_mul hZg hSg (hH _)
        (mul_nonneg hZ.le (pow_nonneg (hH _) _))) (hw_le w hw) (hH _)
        (mul_nonneg (mul_nonneg hZ.le (pow_nonneg (hH _) _))
          (mul_nonneg hM.le (pow_nonneg (mul_nonneg (mul_nonneg hZ.le hD.le) (pow_nonneg (hH _) _)) _)))
    _ = Z * M * (Z * D) ^ em * D * H g ^ (ez + (ez + 1) * em) := by
      rw [mul_pow, pow_add (H g) ez ((ez + 1) * em), pow_mul (H g) (ez + 1) em]
      ring

end Langlands.Global.RepresentationGrowth
