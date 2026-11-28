import Langlands.Global.AdelicLeviFibreSmoothing
import Langlands.Global.LeftCosetKernelPairing
import Langlands.Global.AdelicFiniteVolumeProof

/-! # Levi kernels for the transpose of fibre smoothing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "X₁" => NormOneRationalQuotient F M
local notation "dq₁" => normOneRationalQuotientHaarMeasure F M
local notation "Q₊" => PositiveRationalQuotient F M T i
local notation "dq" => positiveRationalQuotientHaarMeasure F M T i
local notation "V" => Lp ℂ 2 dq
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "ι" => map F M G (fam.l J ≫ fam.p J)
local notation "δ" => fam.leviModulus J

/-- The radical kernel translated by a positive point, for the transpose of Levi fibre smoothing. -/
def leviFibrePairingKernel (β : C_c(A, ℂ)) (g : A) (b : Pos) : C_c(AM, ℂ) :=
  let L := fam.radicalKernelCc J β g 1
  let E := Homeomorph.mulLeft (pp b)
  ⟨⟨L ∘ E, L.continuous.comp E.continuous⟩, L.hasCompactSupport.comp_homeomorph E⟩

@[simp]
theorem leviFibrePairingKernel_apply (β : C_c(A, ℂ)) (g : A) (b : Pos) (m : AM) :
    fam.leviFibrePairingKernel J T i β g b m = fam.radicalKernel J β g 1 (pp b * m) := rfl

/-- The positive translate retains the Levi test function property of the radical kernel. -/
theorem isAdelicTestFunction_leviFibrePairingKernel (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    (β : C_c(A, ℂ)) (hβ : IsAdelicTestFunction F G β) (g : A) (b : Pos) :
    IsAdelicTestFunction F M (fam.leviFibrePairingKernel J T i β g b) := by
  have hL := fam.isAdelicTestFunction_radicalKernel J hAvg hβ g 1
  have hκ := isAdelicTestFunction_comp_mul_mul (fam.leviSmooth J) hL (pp b) 1
  simpa only [mul_one, ← leviFibrePairingKernel_apply] using hκ

/-- Recentring the positive coordinate cancels the positive point in the radical kernel,
leaving the covariance modulus and a translation of the partial convolution evaluation. -/
theorem normOnePartialConvolution_leviFibrePairingKernel_mul_positive
    (hc : IsCentral i) (β : C_c(A, ℂ)) (g : A) (a b : Pos) (t : Q₊ → ℂ) (y : AM) :
    normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β (ι (pp a) * g) (a * b)) t y =
      (δ (pp a) : ℝ) • normOnePartialConvolution T i (fam.radicalKernelCc J β g 1) t (y * pp b) := by
  unfold normOnePartialConvolution
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  have harg : (pp a)⁻¹ * (pp (a * b) * ((n : AM)⁻¹ * y)) = (n : AM)⁻¹ * (y * pp b) := by
    rw [map_mul, mul_assoc (pp a) (pp b), inv_mul_cancel_left,
      (positivePointMap_commute F M T i hc b _).eq, mul_assoc]
  dsimp only
  rw [leviFibrePairingKernel_apply, radicalKernel_mul_levi, harg]
  simp only [radicalKernelCc_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, mul_assoc]

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

local notation "E" => positiveQuotientMeasurableEquiv F M T i hi I e hc

/-- At a fixed positive point, transpose fibre smoothing from the \(L^2\) class to the
bounded norm-one test. -/
theorem integral_leviFibreSmoothingIntegrand_mul_conj (β : C_c(A, ℂ)) (g : A) (b : Pos)
    (v : V) (t : X₁ → ℂ) (ht : Measurable t) (C : ℝ) (hC : ∀ ξ, ‖t ξ‖ ≤ C) :
    ∫ ξ : X₁, fam.leviFibreSmoothingIntegrand J T i β g b (Quotient.out ξ) v *
        starRingEnd ℂ (t ξ) ∂dq₁ =
      (δ (pp b) : ℝ)⁻¹ • ∫ q : X₁, (v : Q₊ → ℂ) (E q) *
        starRingEnd ℂ (normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β g b)
          (t ∘ (E).symm) ((Quotient.out q : A₁) : AM)) ∂dq₁ := by
  let Γ₁ := rationalNormOneSubgroup F M
  let K := fam.leviFibrePairingKernel J T i β g b
  let K₁ (z : A₁) := K (z : AM)
  let v₁ (ξ : X₁) := (v : Q₊ → ℂ) (E ξ)
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M
    (fam.isCompatible J).levi.isConnectedReductive
  have hmp := measurePreserving_positiveQuotient F M T i hi I e hc
  let : IsFiniteMeasure dq := by
    rw [← hmp.map_eq]
    infer_instance
  have hv₁ : Integrable v₁ dq₁ :=
    hmp.integrable_comp_of_integrable ((Lp.memLp v).integrable (by norm_num))
  have hK₁ : Integrable K₁ (Measure.haar : Measure A₁) :=
    (K.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (K.hasCompactSupport.comp_isClosedEmbedding (isClosed_normOneSubgroup F M).isClosedEmbedding_subtypeVal)
  have hq (x : A₁) : E (LeftCosetSpace.mk Γ₁ x) =
      LeftCosetSpace.mk (positiveRationalSubgroup F M T i) (x : AM) :=
    positiveQuotientHomeomorph_mk F M T i hi I e hc x
  have hLeft (x : A₁) :
      fam.leviFibreSmoothingIntegrand J T i β g b x v =
        (δ (pp b) : ℝ)⁻¹ • ∫ z : A₁, K₁ (x⁻¹ * z) * v₁ (LeftCosetSpace.mk Γ₁ z) ∂Measure.haar := by
    unfold leviFibreSmoothingIntegrand normOnePartialConvolution
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [leviFibreSmoothingKernel_apply, Complex.conj_conj, K₁, K, v₁, hq,
      leviFibrePairingKernel_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  have hRight (y : A₁) :
      starRingEnd ℂ (normOnePartialConvolution T i K (t ∘ (E).symm) (y : AM)) =
        ∫ x : A₁, K₁ (x⁻¹ * y) * starRingEnd ℂ (t (LeftCosetSpace.mk Γ₁ x)) ∂Measure.haar := by
    unfold normOnePartialConvolution
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← hq x]
    simp only [map_mul, Complex.conj_conj, Function.comp_apply, MeasurableEquiv.symm_apply_apply,
      K₁, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ = (δ (pp b) : ℝ)⁻¹ • ∫ q : X₁, v₁ q *
    starRingEnd ℂ (normOnePartialConvolution T i K (t ∘ (E).symm) ((Quotient.out q : A₁) : AM)) ∂dq₁
  simp only [hLeft, hRight, smul_mul_assoc, integral_smul]
  exact congrArg (((δ (pp b) : ℝ)⁻¹) • ·)
    (LeftCosetSpace.integral_integral_kernel_swap Γ₁ (isDiscrete_rationalNormOneSubgroup F M)
      K₁ hK₁ v₁ t hv₁ ht C hC)

end Langlands.Global.StandardParabolicFamily
