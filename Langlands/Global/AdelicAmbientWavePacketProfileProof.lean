import Langlands.Global.AdelicAmbientWavePacketProfileStatement
import Langlands.Global.AdelicCharacterParameterEquivalences
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # The ambient spectral profile is a scaled inverse Schwartz Fourier transform -/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure TensorProduct
open scoped CategoryTheory.MonObj ENNReal FourierTransform RealInnerProductSpace SchwartzMap TensorProduct

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre InducedInnerProductIntegrable

section Coordinates

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {m : ℕ} (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G)

local notation "V" => EuclideanSpace ℝ (Fin m)

private def coordinatesLinearEquiv : RealCharacterDual F G ≃ₗ[ℝ] (Fin m → ℝ) := by
  refine LinearEquiv.ofBijective
    { toFun := parameterCoordinates F G eG
      map_add' := parameterCoordinates_add eG
      map_smul' := fun t H => by ext j; simp [parameterCoordinates] }
    ⟨parameterCoordinates_injective eG, ?_⟩
  intro y
  let B := (Pi.basisFun ℝ (Fin m)).map eG
  let L : Module.Dual ℝ (RealCharacterParameter F G) := B.constr ℝ y
  refine ⟨realCharacterDualEquivParameterDual.symm L, funext fun j => ?_⟩
  change parameterCoordinates F G eG (realCharacterDualEquivParameterDual.symm L) j = y j
  simp only [parameterCoordinates, ← realCharacterDualEquivParameterDual_apply, LinearEquiv.apply_symm_apply]
  simpa only [B, Module.Basis.map_apply, Pi.basisFun_apply] using (B.constr_basis ℝ y j)

omit [NumberField F] in
private theorem parameterPairing_coordinates (x : Fin m → ℝ) (H : RealCharacterDual F G) :
    realParameterPairing F G (eG x) H = ∑ j, x j * parameterCoordinates F G eG H j := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin m)).sum_repr x]
  simp only [_root_.map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Pi.basisFun_repr, Pi.basisFun_apply, parameterCoordinates]

private def fourierCoordinates : RealCharacterDual F G ≃L[ℝ] V := by
  let E := (coordinatesLinearEquiv eG).trans (PiLp.continuousLinearEquiv 2 ℝ _).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (RealCharacterDual F G) := E.symm.finiteDimensional
  exact E.toContinuousLinearEquiv

private theorem real_inner_coordinates (x : V) (H : RealCharacterDual F G) :
    ⟪x, fourierCoordinates eG H⟫ = realParameterPairing F G (eG (WithLp.ofLp x)) H := by
  rw [parameterPairing_coordinates eG]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  change parameterCoordinates F G eG H j * x.ofLp j = x.ofLp j * parameterCoordinates F G eG H j
  exact mul_comm _ _

omit [NumberField F] in
private theorem imaginaryPairing (x : RealCharacterParameter F G) (H : RealCharacterDual F G) :
    complexParameterPairing F G (imaginaryParameter F G x) H =
      (realParameterPairing F G x H : ℂ) * Complex.I := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ =>
    change ((t : ℂ) * Complex.I) * (H χ : ℂ) = ((t * H χ : ℝ) : ℂ) * Complex.I
    simp only [Complex.ofReal_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Complex.ofReal_add, add_mul, hx, hy]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)

local notation "A₀" => canonicalSubgroup F G
local notation "μA" => positiveCentreHaarMeasure F G hG

local instance {X : Type*} [MeasurableSpace X] : MeasurableSpace (Multiplicative X) :=
  ‹MeasurableSpace X›

local instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] :
    BorelSpace (Multiplicative X) := ‹BorelSpace X›

private def centreFourierChart : A₀ ≃ₜ* Multiplicative V := by
  let L := positiveCentreLogEquiv F G hG
  let D := fourierCoordinates eG
  let Dm : Multiplicative (RealCharacterDual F G) ≃ₜ* Multiplicative V :=
    { toMulEquiv := (D : RealCharacterDual F G ≃+ V).toMultiplicative
      continuous_toFun := D.continuous
      continuous_invFun := D.symm.continuous }
  exact L.trans Dm

private theorem centreFourierChart_apply (a : A₀) :
    (centreFourierChart eG hG a).toAdd = fourierCoordinates eG (characterLog F G a.val) := by
  change fourierCoordinates eG (positiveCentreLogEquiv F G hG a).toAdd = _
  rw [positiveCentreLogEquiv_apply]
  rfl

private theorem isAddHaarMeasure_centreChart :
    IsAddHaarMeasure (Measure.map (fun a => (centreFourierChart eG hG a).toAdd) μA) := by
  let mulMeasure : Measure (Multiplicative V) := Measure.map (centreFourierChart eG hG) μA
  have : mulMeasure.IsHaarMeasure := (centreFourierChart eG hG).isHaarMeasure_map μA
  exact
    { toIsFiniteMeasureOnCompacts := (inferInstance : IsFiniteMeasureOnCompacts mulMeasure)
      toIsOpenPosMeasure := (inferInstance : IsOpenPosMeasure mulMeasure)
      map_add_left_eq_self := fun v => map_mul_left_eq_self mulMeasure (Multiplicative.ofAdd v) }

end Coordinates

set_option maxHeartbeats 800000 in
/-- In dual coordinates the profile is the inverse Fourier transform of a Schwartz function.
The target measure is the actual positive-centre Haar measure, not a new normalization. -/
theorem ambientWavePacketProfile_squareIntegrable : AmbientWavePacketProfileStatement := by
  intro F _ _ G _ _ hG m eG b hb hbc
  let V := EuclideanSpace ℝ (Fin m)
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)
  have hs : HasCompactSupport (b ∘ E) := hbc.comp_homeomorph E.toHomeomorph
  let B : 𝓢(V, ℂ) := hs.toSchwartzMap (hb.comp E.contDiff)
  let c : ℂ := (((2 * Real.pi)⁻¹ ^ m : ℝ) : ℂ)
  have h2π : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero h2π.ne'))
  let d : ℝ := (2 * Real.pi)⁻¹
  have hd : d ≠ 0 := inv_ne_zero h2π.ne'
  let dil : V ≃L[ℝ] V :=
    ({ toFun := fun v => d • v
       invFun := fun v => d⁻¹ • v
       left_inv := fun v => by dsimp only; rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
       right_inv := fun v => by dsimp only; rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
       map_add' := fun v w => smul_add d v w
       map_smul' := fun t v => smul_comm d t v } : V ≃ₗ[ℝ] V).toContinuousLinearEquiv
  let S : 𝓢(V, ℂ) := c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ dil (𝓕⁻ B)
  have hS (g : AdelicGroupPoints F G) :
      ambientWavePacketProfile eG b g = S (fourierCoordinates eG (characterLog F G g)) := by
    unfold ambientWavePacketProfile
    rw [spectralMeasure, integral_smul_measure]
    have hconst : ((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ m).toReal = (2 * Real.pi)⁻¹ ^ m := by
      rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal h2π.le]
    rw [hconst, Complex.real_smul]
    change c * _ = _
    simp only [S, _root_.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, smul_eq_mul, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    congr 1
    rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp
      (E.symm.toHomeomorph.measurableEmbedding)]
    apply integral_congr_ae
    filter_upwards with x
    change b x * parameterPower F G (imaginaryParameter F G (eG x)) g =
      Complex.exp (↑(2 * Real.pi * ⟪(WithLp.toLp 2 x : V),
        d • fourierCoordinates eG (characterLog F G g)⟫) * Complex.I) * b x
    rw [real_inner_smul_right, real_inner_coordinates eG]
    have hcancel (u : ℝ) : 2 * Real.pi * (d * u) = u := by
      rw [← mul_assoc, mul_inv_cancel₀ h2π.ne', one_mul]
    rw [hcancel, parameterPower, imaginaryPairing, mul_comm]
  have hcont : Continuous (ambientWavePacketProfile eG b) := by
    exact (S.continuous.comp ((fourierCoordinates eG).continuous.comp
      (continuous_characterLog F G))).congr (fun g => (hS g).symm)
  let centreMeasure := positiveCentreHaarMeasure F G hG
  let C : canonicalSubgroup F G → V := fun a => (centreFourierChart eG hG a).toAdd
  let μV : Measure V := Measure.map C centreMeasure
  have : IsAddHaarMeasure μV := isAddHaarMeasure_centreChart eG hG
  have hmem : MemLp (fun a : canonicalSubgroup F G => ambientWavePacketProfile eG b a.val) 2 centreMeasure := by
    have hC : Continuous C := (centreFourierChart eG hG).continuous
    have h := (S.memLp 2 μV).comp_measurePreserving (⟨hC.measurable, rfl⟩ :
      MeasurePreserving C centreMeasure μV)
    convert h using 1
    funext a
    exact (hS a.val).trans (congrArg S (centreFourierChart_apply eG hG a).symm)
  refine ⟨hcont, hmem, fun hb0 => ?_⟩
  have hS0 : (S : V → ℂ) ≠ 0 := by
    intro h0
    apply hb0
    have hF : (𝓕⁻ B : 𝓢(V, ℂ)) = 0 := by
      ext v
      obtain ⟨y, rfl⟩ := dil.surjective v
      have hv := congrFun h0 y
      change c * (𝓕⁻ B : 𝓢(V, ℂ)) (dil y) = 0 at hv
      exact (mul_eq_zero.mp hv).resolve_left hc
    have hB : B = 0 := calc
      B = 𝓕 (𝓕⁻ B : 𝓢(V, ℂ)) := (FourierTransform.fourier_fourierInv_eq B).symm
      _ = 0 := by rw [hF, FourierTransform.fourier_zero]
    funext x
    exact congrArg (fun f : 𝓢(V, ℂ) => f (E.symm x)) hB
  let f : canonicalSubgroup F G → ℂ := fun a => ambientWavePacketProfile eG b a.val
  have hf : Continuous f := hcont.comp continuous_subtype_val
  have hfn : ∃ a, f a ≠ 0 := by
    by_contra! h
    apply hS0
    funext u
    obtain ⟨a, ha⟩ := (centreFourierChart eG hG).surjective (Multiplicative.ofAdd u)
    have hu : (centreFourierChart eG hG a).toAdd = u := congrArg Multiplicative.toAdd ha
    rw [← hu, centreFourierChart_apply]
    exact (hS a.val).symm.trans (h a)
  have hint := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  apply (integral_pos_iff_support_of_nonneg (fun a => sq_nonneg ‖f a‖) hint).mpr
  obtain ⟨a, ha⟩ := hfn
  have hopen : IsOpen (Function.support (fun a => ‖f a‖ ^ 2)) := (hf.norm.pow 2).isOpen_support
  exact hopen.measure_pos centreMeasure
    ⟨a, by simpa [Function.mem_support, pow_ne_zero_iff] using ha⟩

end Langlands.Global
