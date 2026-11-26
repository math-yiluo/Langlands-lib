import Langlands.Global.AdelicNormalizedConvolutionCompact
import Langlands.Global.AdelicInducedConvolutionFiniteSpanStatement
import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Parabolic covariance and moderate growth of the integrated induced action -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Global.RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

local notation "H" => AdelicGroupPoints F G
local notation "Param" => ComplexCharacterParameter F P
local notation "haar" => (Measure.haar : Measure H)

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The pointwise multiplier in the induced translate is the exponential of the height increment. -/
theorem IsIwasawaCompact.inducedRightTranslate_eq_mul_exp_sub (hK : IsIwasawaCompact p K)
    (lam : Param) (h : H) (v : H → ℂ) (g : H) :
    hK.inducedRightTranslate lam h v g = v (g * h) * Complex.exp
      (complexParameterPairing F P lam (hK.height (g * h) - hK.height g)) := by
  unfold IsIwasawaCompact.inducedRightTranslate IsIwasawaCompact.parameterTwist
    IsIwasawaCompact.heightPower
  simp only [map_sub, map_neg, LinearMap.neg_apply]
  rw [sub_eq_add_neg, Complex.exp_add]
  ring

variable (hK : IsIwasawaCompact p K)

/-- Left parabolic covariance of a function passes to its induced translates. -/
theorem IsIwasawaCompact.inducedRightTranslate_map_mul (lam : Param) (v : H → ℂ)
    (q : AdelicGroupPoints F P) (s : ℂ)
    (hv : ∀ g, v (map F P G p q * g) = s * v g) (g h : H) :
    hK.inducedRightTranslate lam h v (map F P G p q * g) =
      s * hK.inducedRightTranslate lam h v g := by
  rw [hK.inducedRightTranslate_eq_mul_exp_sub, hK.inducedRightTranslate_eq_mul_exp_sub,
    mul_assoc (map F P G p q) g h, hv, hK.height_map_mul, hK.height_map_mul,
    add_sub_add_left_eq_sub, mul_assoc]

variable [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The twist multiplier on a compact set of right translates is bounded independently of
where the translate is evaluated. -/
theorem IsIwasawaCompact.exists_norm_inducedRightTranslate_le (lam : Param)
    {C : Set H} (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : H → ℂ) (g h : H), h ∈ C →
      ‖hK.inducedRightTranslate lam h v g‖ ≤ B * ‖v (g * h)‖ := by
  obtain ⟨B, hB⟩ := (hK.isCompact.mul hC).exists_bound_of_continuousOn
    (hK.continuous_heightPower lam).continuousOn
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), fun v g h hh => ?_⟩
  obtain ⟨k, hk, he⟩ := hK.exists_height_mul_eq_add g h
  rw [hK.inducedRightTranslate_eq_mul_exp_sub, he, add_sub_cancel_left, norm_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (hB (k * h) ⟨k, hk, h, hh, rfl⟩).trans (le_max_right _ _)

/-- A continuous moderately growing input remains moderately growing under the compactly
supported integrated action, for every complex parameter. -/
theorem IsIwasawaCompact.hasModerateGrowthFunction_inducedConvolution (lam : Param)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) {φ v : H → ℂ}
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ)
    (hv : HasModerateGrowthFunction F G rho v) :
    HasModerateGrowthFunction F G rho (hK.inducedConvolution lam φ v) := by
  obtain ⟨B, hB, hmult⟩ := hK.exists_norm_inducedRightTranslate_le lam hsupp
  obtain ⟨r, _, htrans⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hv
  obtain ⟨D, hD, hgrow⟩ := htrans (tsupport φ) hsupp
  have hφi : Integrable (fun h => ‖φ h‖) haar := (hφ.integrable_of_hasCompactSupport hsupp).norm
  let A := (∫ h, ‖φ h‖ ∂haar) + 1
  have hmass : 0 ≤ ∫ h, ‖φ h‖ ∂haar := integral_nonneg fun _ => norm_nonneg _
  have hA : 0 < A := by dsimp [A]; positivity
  have hb (g : H) : ‖hK.inducedConvolution lam φ v g‖ ≤
      (A * (B * D)) * adelicHeightAtLeastOne rho g ^ r := by
    let a := adelicHeightAtLeastOne rho g ^ r
    have ha : 0 ≤ a := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
    have hle (h : H) : ‖φ h * hK.inducedRightTranslate lam h v g‖ ≤ ‖φ h‖ * (B * (D * a)) := by
      rw [norm_mul]
      by_cases hh : h ∈ tsupport φ
      · exact mul_le_mul_of_nonneg_left ((hmult v g h hh).trans (mul_le_mul_of_nonneg_left
          (hgrow g h hh) hB.le)) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hh, norm_zero, zero_mul, zero_mul]
    change ‖∫ h, φ h * hK.inducedRightTranslate lam h v g ∂haar‖ ≤ _
    refine (norm_integral_le_of_norm_le (hφi.mul_const (B * (D * a)))
      (Eventually.of_forall hle)).trans ?_
    rw [integral_mul_const]
    calc
      _ ≤ A * (B * (D * a)) := mul_le_mul_of_nonneg_right
        (by dsimp [A]; linarith) (mul_nonneg hB.le (mul_nonneg hD.le ha))
      _ = _ := by change A * (B * (D * a)) = A * (B * D) * a; ring
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hmat (g : H) : adelicMatrix F G rho g = 1 := by
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    let C := max 1 (AdelicMatrixHeight.height F 0 1)
    have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨A * (B * D) * C ^ r, mul_pos (mul_pos hA (mul_pos hB hD))
      (Real.rpow_pos_of_pos hC _), 0, fun g => ?_⟩
    simpa only [Real.rpow_zero, mul_one, adelicHeightAtLeastOne, adelicHeight, hmat, C] using hb g
  · let C : ℝ := (N : ℝ) ^ (∑ w : NumberField.InfinitePlace F, w.mult)
    have hC : 0 < C := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨A * (B * D) * C ^ r, mul_pos (mul_pos hA (mul_pos hB hD))
      (Real.rpow_pos_of_pos hC _), r, fun g => (hb g).trans_eq ?_⟩
    rw [adelicHeightAtLeastOne_eq hN, adelicHeight_eq_scalar_mul_sourceNorm,
      Real.mul_rpow hC.le (adelicSourceNorm_pos F G rho hN g).le]
    ring

/-- Left invariance under the parabolic quotient subgroup and equivariance under the split
component pass to convolution. -/
def InducedConvolutionParabolicCovarianceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (v φ : AdelicGroupPoints F G → ℂ),
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) v →
    IsSplitComponentEquivariant p l v → ∀ lam : ComplexCharacterParameter F P,
      IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (hK.inducedConvolution lam φ v) ∧
      IsSplitComponentEquivariant p l (hK.inducedConvolution lam φ v)

/-- Every multiplier in the parabolic quotient subgroup comes from `P(𝔸)`. -/
theorem inducedConvolutionParabolicCovariance : InducedConvolutionParabolicCovarianceStatement := by
  intro F _ _ G P M U _ _ _ _ _ _ p _ iU l K hK v φ hleft hsplit lam
  have hP : parabolicQuotientSubgroup F p iU l ≤ (map F P G p).toMonoidHom.range := by
    apply sup_le
    · rintro _ ⟨u, rfl⟩
      exact ⟨map F U P iU u, (map_comp_apply_of_hom iU u).symm⟩
    · rintro _ ⟨m, rfl⟩
      exact ⟨map F M P l (rational F M m), (map_comp_apply_of_hom l (rational F M m)).symm⟩
  refine ⟨?_, ?_⟩
  · intro g hg x
    obtain ⟨q, hq⟩ := hP hg
    have hinv (y : AdelicGroupPoints F G) : v (map F P G p q * y) = 1 * v y := by
      rw [show map F P G p q = g from hq, hleft g hg, one_mul]
    rw [← show map F P G p q = g from hq,
      hK.integral_translate_left_equivariant φ v lam q 1 hinv, one_mul]
  · exact fun a ha g => hK.integral_translate_left_equivariant φ v lam (map F M P l a) _ (hsplit a ha) g

end Langlands.Global.AdelicGroupPoints
