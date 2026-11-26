import Langlands.Global.AdelicWavePacketAmbientLiftStatement
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicInducedInnerProductGramCoordinateProof
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Fourier inversion of the ambient wave-packet profile on the positive centre -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct FourierTransform NNReal ENNReal InnerProductSpace

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre InducedInnerProductSesquilinear
open InducedInnerProductGram

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin m)
local notation "τ" => (2 * Real.pi)

private theorem twoPi_pos : 0 < τ := mul_pos (by norm_num) Real.pi_pos

private def dualCoordinates (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) :
    RealCharacterDual F G ≃L[ℝ] (Fin m → ℝ) := by
  let l := LinearEquiv.ofBijective (coordinateMap e)
    ⟨coordinateMap_injective e, coordinateMap_surjective e⟩
  exact { toLinearEquiv := l
          continuous_toFun := continuous_parameterCoordinates F G e
          continuous_invFun := l.symm.toLinearMap.continuous_of_finiteDimensional }

private theorem realParameterPairing_coordinates
    (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (z : Fin m → ℝ)
    (H : RealCharacterDual F G) :
    realParameterPairing F G (e z) H = ⟪WithLp.toLp 2 z, WithLp.toLp 2 (dualCoordinates e H)⟫_ℝ := by
  have h : (realParameterPairing F G).flip H ∘ₗ e.toLinearMap =
      Fintype.linearCombination ℝ (dualCoordinates e H) := by
    apply (Pi.basisFun ℝ (Fin m)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.flip_apply, Fintype.linearCombination_apply_single, one_smul]
    rfl
  have hz := LinearMap.congr_fun h z
  rw [Fintype.linearCombination_apply] at hz
  change realParameterPairing F G (e z) H = _ at hz
  rw [hz, PiLp.inner_apply]
  simp [smul_eq_mul, mul_comm]

omit [NumberField F] in
private theorem complexParameterPairing_imaginary (ν : RealCharacterParameter F G)
    (H : RealCharacterDual F G) :
    complexParameterPairing F G (imaginaryParameter F G ν) H =
      (realParameterPairing F G ν H : ℂ) * Complex.I := by
  induction ν using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [imaginaryParameter, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      complexParameterPairing_tmul, realParameterPairing_tmul, Complex.ofReal_mul]
    change ((t : ℂ) * Complex.I) * (H χ : ℂ) = (t : ℂ) * (H χ : ℂ) * Complex.I
    ring
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, Complex.ofReal_add, add_mul]

section Centre

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
  (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G)

private def scaledDualCoordinates : RealCharacterDual F G ≃L[ℝ] V :=
  (dualCoordinates e).trans <| (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := V) (Units.mk0 τ⁻¹ (inv_ne_zero twoPi_pos.ne')))

private def centreCoordinates : canonicalSubgroup F G ≃ₜ V :=
  (positiveCentreLogEquiv F G hG).toHomeomorph.trans
    (scaledDualCoordinates e).toHomeomorph

private theorem centreCoordinates_apply (a : canonicalSubgroup F G) :
    centreCoordinates hG e a = τ⁻¹ • WithLp.toLp 2 (dualCoordinates e (characterLog F G a.val)) := by
  change scaledDualCoordinates e ((positiveCentreLogEquiv F G hG a).toAdd) = _
  rw [positiveCentreLogEquiv_apply]
  rfl

private theorem centreCoordinates_mul (a a' : canonicalSubgroup F G) :
    centreCoordinates hG e (a * a') = centreCoordinates hG e a + centreCoordinates hG e a' := by
  change scaledDualCoordinates e ((positiveCentreLogEquiv F G hG (a * a')).toAdd) = _
  rw [map_mul]
  exact (scaledDualCoordinates e).map_add _ _

private theorem parameterPower_centreCoordinates (a : canonicalSubgroup F G) (z : Fin m → ℝ) :
    parameterPower F G (imaginaryParameter F G (e z)) a.val =
      Complex.exp ((τ * ⟪WithLp.toLp 2 z, centreCoordinates hG e a⟫_ℝ : ℝ) * Complex.I) := by
  rw [parameterPower, complexParameterPairing_imaginary, realParameterPairing_coordinates,
    centreCoordinates_apply, real_inner_smul_right, ← mul_assoc,
    mul_inv_cancel₀ twoPi_pos.ne', one_mul]

private def coefficientSchwartz (b : (Fin m → ℝ) → ℂ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) : SchwartzMap V ℂ := by
  let q := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)
  exact (hbc.comp_homeomorph q.toHomeomorph).toSchwartzMap (hb.comp q.contDiff)

private theorem ambientWavePacketProfile_eq_fourierInv
    (b : (Fin m → ℝ) → ℂ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (a : canonicalSubgroup F G) :
    ambientWavePacketProfile e b a.val = (τ⁻¹ ^ m : ℝ) •
      (𝓕⁻ (coefficientSchwartz b hb hbc)) (centreCoordinates hG e a) := by
  rw [ambientWavePacketProfile, spectralMeasure, integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal twoPi_pos.le, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq']
  congr 1
  rw [← (PiLp.volume_preserving_ofLp (Fin m)).integral_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with z
  rw [parameterPower_centreCoordinates hG e]
  change b z.ofLp * Complex.exp ((τ * ⟪z, centreCoordinates hG e a⟫_ℝ : ℝ) * Complex.I) = _
  exact mul_comm _ _

end Centre

/-- Fourier inversion of the ambient profile on the actual positive split centre, with the
positive Haar normalization factor for the chosen parameter chart. -/
def AmbientWavePacketProfileFourierInversionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {m : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G),
    ∃ c : ℝ, 0 < c ∧ ∀ (b : (Fin m → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
      ∀ ν : RealCharacterParameter F G,
      let f (a : canonicalSubgroup F G) :=
        ambientWavePacketProfile e b a.val *
          starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)
      Integrable f (positiveCentreHaarMeasure F G hG) ∧
        (∫ a, f a ∂(positiveCentreHaarMeasure F G hG)) = (c : ℂ) * b (e.symm ν)

/-- Fourier inversion in the real logarithmic coordinates of the positive split centre. -/
theorem ambientWavePacketProfileFourierInversion : AmbientWavePacketProfileFourierInversionStatement := by
  intro F _ _ G _ _ hG m e
  let q := centreCoordinates hG e
  let centreMeasure := positiveCentreHaarMeasure F G hG
  have : (Measure.map q centreMeasure).IsAddHaarMeasure :=
    isAddHaarMeasure_map_of_map_mul centreMeasure q (centreCoordinates_mul hG e)
  let k := Measure.addHaarScalarFactor (Measure.map q centreMeasure) (volume : Measure (EuclideanSpace ℝ (Fin m)))
  have hk : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hq : MeasurePreserving q centreMeasure (k • volume) :=
    ⟨q.continuous.measurable, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨(k : ℝ) * τ⁻¹ ^ m, mul_pos (NNReal.coe_pos.mpr hk) (pow_pos (inv_pos.mpr twoPi_pos) _), ?_⟩
  intro b hb hbc ν
  dsimp only
  let B := coefficientSchwartz b hb hbc
  let w : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (e.symm ν)
  let phase : EuclideanSpace ℝ (Fin m) → ℂ := fun y => Complex.exp ((-2 * Real.pi * ⟪y, w⟫_ℝ : ℝ) * Complex.I)
  let ψ : EuclideanSpace ℝ (Fin m) → ℂ := fun y => phase y * (𝓕⁻ B) y
  have hψ : Integrable ψ := by
    refine (𝓕⁻ B).integrable.mono ?_ ?_
    · exact (show Continuous phase by unfold phase; fun_prop).mul (𝓕⁻ B).continuous
        |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        have hunit : ‖phase y‖ = 1 := Complex.norm_exp_ofReal_mul_I _
        change ‖phase y * (𝓕⁻ B) y‖ ≤ ‖(𝓕⁻ B) y‖
        rw [norm_mul, hunit, one_mul])
  let inverse : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ := 𝓕⁻ B
  have hI : (∫ y, ψ y) = b (e.symm ν) := by
    calc
      (∫ y, ψ y) = (𝓕 ⇑inverse) w :=
        (Real.fourier_eq' _ _).symm
      _ = b (e.symm ν) := by
        rw [← SchwartzMap.fourier_coe]
        change (𝓕 (𝓕⁻ B)) w = _
        rw [FourierTransform.fourier_fourierInv_eq]
        rfl
  have hphase (a : canonicalSubgroup F G) :
      starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val) = phase (q a) := by
    rw [← e.apply_symm_apply ν, parameterPower_centreCoordinates hG e]
    change starRingEnd ℂ (Complex.exp ((τ * ⟪w, q a⟫_ℝ : ℝ) * Complex.I)) = _
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    rw [real_inner_comm w (q a)]
    simp only [mul_neg, neg_mul, Complex.ofReal_neg]
  have hfun : (fun a : canonicalSubgroup F G => ambientWavePacketProfile e b a.val *
      starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)) =
      fun a => (τ⁻¹ ^ m : ℝ) • ψ (q a) := by
    funext a
    rw [ambientWavePacketProfile_eq_fourierInv hG e b hb hbc a, hphase]
    simp only [Complex.real_smul, ψ, B, q]
    ring
  rw [hfun]
  constructor
  · exact ((hq.integrable_comp_emb q.measurableEmbedding).mpr hψ.smul_measure_nnreal).smul (τ⁻¹ ^ m : ℝ)
  · rw [integral_smul, hq.integral_comp q.measurableEmbedding ψ, integral_smul_nnreal_measure, hI]
    simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
    ring

end Langlands.Global
