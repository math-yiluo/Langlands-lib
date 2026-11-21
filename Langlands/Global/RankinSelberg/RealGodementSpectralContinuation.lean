import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Global.RankinSelberg.RealGodementSpectralStep
import Langlands.Global.RankinSelberg.RealRankZeroParameter

/-! # Uniform real Jacquet continuation in every positive rank -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient upperUnipotent_one_subsingleton)
open Langlands.RankinSelberg.RankOneGammaTwist (weylLong_one)
open Langlands.Whittaker
open Filter MeasureTheory Metric Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula RealGodementProfiles RealJacquetFrobenius RealRankZero

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

/-- The determinant Haar measure and the prescribed upper-entry Haar measure
admit a compatible real quotient measure in every rank. -/
theorem nonempty_realQuotientMeasureData (t : ℕ) (a : ℝˣ) :
    Nonempty (RealQuotientMeasureData t) := by
  let H := GeneralLinear.upperUnipotent (t + 1) ℝ
  have hH : IsClosed (H : Set (Langlands.GeneralLinear (t + 1) ℝ)) := UpperUnipotent.isClosed
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology ↥(H : Set (Langlands.GeneralLinear (t + 1) ℝ)))
  let μ := realMatrixHaar (t + 1)
  let ν := upperStepHaar t a
  let : μ.IsHaarMeasure := realMatrixHaar_isHaar _
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : ν.IsHaarMeasure := upperStepHaar_isHaar t a
  let : ν.IsMulRightInvariant := upperStepHaar_isMulRightInvariant t a
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  obtain ⟨q, hq⟩ := Langlands.QuotientIntegration.compatibleMeasureExists H hH μ ν
  exact ⟨⟨μ, inferInstance, ν, inferInstance, inferInstance, q, hq⟩⟩

local notation "G" => Langlands.GeneralLinear 1 ℝ
local notation "N" => GeneralLinear.upperUnipotent 1 ℝ
local notation "U" => Matrix.unitaryGroup (Fin 1) ℝ
local notation "P" => (Fin 1 → ℂ)
local notation "M" => Matrix (Fin 1) (Fin 1) ℝ
local notation "Dᵣ" => RealLocalWhittaker.iteratedRightDerivative 0

private local instance : Subsingleton N := upperUnipotent_one_subsingleton

private theorem upperStepHaar_rankOne_univ (a : ℝˣ) : upperStepHaar 0 a univ = 1 := by
  let : IsEmpty (UpperEntryPair 1) := ⟨fun ij => (ne_of_lt ij.2) (Subsingleton.elim _ _)⟩
  let : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  rw [upperStepHaar, Measure.map_apply (upperEntryCoordinates (K := ℝ) 1).symm.measurable MeasurableSet.univ,
    preimage_univ, upperEntryProductMeasure, Measure.pi_univ, Finset.prod_of_isEmpty]

/-- The positive-phase open-cell integral in rank one equals the section. -/
theorem additiveJacquetIntegral_rankOne (a : ℝˣ) (f : G → ℂ) (g : G) :
    additiveJacquetIntegral (t := 0) a f g = f g := by
  have h (u : N) : additiveJacquetKernel (t := 0) a f g u = f g := by
    rw [Subsingleton.elim u 1]
    simp [additiveJacquetKernel, weylLong_one]
  simp only [additiveJacquetIntegral, h, integral_const, Measure.real, upperStepHaar_rankOne_univ,
    ENNReal.toReal_one, one_smul]

private theorem standardSection_rankOne {p : Fin 1 → Fin 2} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) (z : P) :
    standardSection z φ = φ 1 • characterFunction (charData (p 0) (z 0)) := by
  have hF := (standardSection_mem hφ z).1.1
  have hOne : standardSection z φ (1 : G) = φ 1 := by
    have h := congrFun (compactRestriction_standardSection φ z) (1 : U)
    change standardSection z φ (Unitary.toUnits (1 : U)) = φ 1 at h
    simpa only [map_one] using h
  funext g
  let d : Fin 1 → ℝˣ := fun _ => determinant g
  have hg : GeneralLinear.Iwasawa.diagonalUnits d = g := by
    apply Units.ext
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    rw [GeneralLinear.Iwasawa.diagonalUnits_val]
    simp only [Matrix.diagonal_apply_eq, d, determinant_val_fin_one]
  have h := hF.2 d 1 1
  rw [OneMemClass.coe_one, mul_one, mul_one, hg, hOne] at h
  have hShift : (((1 : ℕ) : ℂ) - 1) / 2 - (((0 : Fin 1) : ℕ) : ℂ) = 0 := by norm_num
  simp only [principalSeriesCharacter, Fin.prod_univ_one, realPositionCharacter_characterList,
    Module.finrank_self, pow_one, hShift, Complex.cpow_zero, mul_one] at h
  rw [h]
  change charFun (p 0) (z 0) (determinant g) * φ 1 =
    φ 1 * characterFunction (charData (p 0) (z 0)) g
  rw [characterFunction, charData_character_apply, mul_comm]

private def rankOneDerivativeFactor (Xs : List M) (z : P) : ℂ :=
  (Xs.map fun X => (X 0 0 : ℂ) * z 0).prod

private theorem rankOneDerivativeFactor_holomorphic (Xs : List M) :
    Differentiable ℂ (rankOneDerivativeFactor Xs) := by
  induction Xs with
  | nil => exact differentiable_const 1
  | cons X Xs ih =>
    exact ((ContinuousLinearMap.proj 0 : P →L[ℂ] ℂ).differentiable.const_mul _).mul ih

private theorem iteratedRightDerivative_rankOne {p : Fin 1 → Fin 2} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) (Xs : List M) (z : P) :
    Dᵣ Xs (standardSection z φ) = rankOneDerivativeFactor Xs z • standardSection z φ := by
  let c := charData (p 0) (z 0)
  rw [standardSection_rankOne hφ z, RealUniformWhittaker.iteratedRightDerivative_smul
    (contMDiff_characterFunction c), smul_comm (rankOneDerivativeFactor Xs z)]
  congr 1
  induction Xs with
  | nil => exact (one_smul ℂ (characterFunction c)).symm
  | cons X Xs ih =>
    have hX : X = X 0 0 • (1 : M) := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    change rightDerivative (matrixModel ℝ 1) X (Dᵣ Xs (characterFunction c)) = _
    rw [ih, rightDerivative_smul (contMDiff_characterFunction c)]
    conv_lhs => rw [hX]
    rw [rightDerivative_smul_left, rightDerivative_characterFunction]
    funext g
    simp only [rankOneDerivativeFactor, List.map_cons, List.prod_cons, Pi.smul_apply, Complex.real_smul,
      smul_eq_mul, c, charData]
    ring

private theorem norm_characterFunction_rankOne (c : RealCharacterData) (g : G) :
    ‖characterFunction c g‖ = |g.val.det| ^ c.exponent.re := by
  let d := determinant g
  change ‖(c.character d : ℂ)‖ = |g.val.det| ^ c.exponent.re
  have hd : 0 < |(d : ℝ)| := abs_pos.mpr d.ne_zero
  rw [c.character_eq, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_abs, div_self hd.ne', one_pow, one_mul]
  rfl

private theorem locallyUniformGrowth_rankOne {p : Fin 1 → Fin 2} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) :
    HasLocallyUniformDerivativeGrowth univ (fun z => standardSection z φ) := by
  intro z _
  let T := ‖z‖ + 1
  obtain ⟨C, n, hC, h⟩ := RealPlaceRestriction.exists_det_rpow_le_realMatrixHeight_of_abs_le
    (n := 1) (by decide) T
  refine ⟨1, zero_lt_one, n, fun Xs => ?_⟩
  obtain ⟨A, hA⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
    (rankOneDerivativeFactor_holomorphic Xs).continuous.continuousOn
  let B := max A 0
  refine ⟨B * (‖φ 1‖ * C), by positivity, fun q hq g => ?_⟩
  have hqT : ‖q‖ ≤ T := by
    have hq' : ‖q - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hq
    calc
      ‖q‖ = ‖q - z + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖q - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ T := by dsimp [T]; linarith
  have hExp : |(q 0).re| ≤ T :=
    (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm q 0).trans hqT)
  rw [iteratedRightDerivative_rankOne hφ, standardSection_rankOne hφ]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_characterFunction_rankOne, charData]
  rw [← mul_assoc]
  have hB : ‖rankOneDerivativeFactor Xs q‖ ≤ B :=
    (hA q (ball_subset_closedBall hq)).trans (le_max_left _ _)
  calc
    _ ≤ (B * ‖φ 1‖) * (C * realMatrixHeight g ^ n) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (h _ hExp g)
        (Real.rpow_nonneg (abs_nonneg _) _) (mul_nonneg (le_max_right _ _) (norm_nonneg _))
    _ = _ := by ring

/-- Rank one starts the uniform Jacquet induction with the two real signs and
the entire family of characters at all complex exponents. -/
theorem hasLocallyUniformRealJacquetFamily_rankOne (a : ℝˣ) : HasLocallyUniformRealJacquetFamily 0 a := by
  intro p φ hφ
  let W (z : P) := standardSection z φ
  have hGrowth := locallyUniformGrowth_rankOne hφ
  have hSmooth (z : P) : ContMDiff (matrixModel ℝ 1) 𝓘(ℝ, ℂ) ∞ (W z) :=
    (standardSection_mem hφ z).1.1.1
  have hLaw (z : P) (u : G) (hu : u ∈ GeneralLinear.upperUnipotent 1 ℝ) (g : G) :
      W z (u * g) = realWhittakerCharacter (-a) u * W z g := by
    have he : u = 1 := congrArg Subtype.val (Subsingleton.elim (⟨u, hu⟩ : N) 1)
    rw [he, one_mul]
    simp [realWhittakerCharacter]
  refine ⟨W, regular_iteratedRightDerivative_of_spectralGrowth W hSmooth hGrowth hLaw, hGrowth, ?_,
    fun z _ g => (additiveJacquetIntegral_rankOne a (W z) g).symm⟩
  intro Xs g
  change Differentiable ℂ (fun z => Dᵣ Xs (standardSection z φ) g)
  simp only [iteratedRightDerivative_rankOne hφ, Pi.smul_apply, smul_eq_mul]
  exact (rankOneDerivativeFactor_holomorphic Xs).mul (differentiable_standardSection φ g)

/-- Real fixed-profile Jacquet integrals continue to all inducing exponents in
every positive rank, with all the locally uniform right derivative estimates. -/
def RealGodementSpectralContinuationStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ), HasLocallyUniformRealJacquetFamily t a

theorem realGodementSpectralContinuation : RealGodementSpectralContinuationStatement := by
  intro t a
  induction t with
  | zero => exact hasLocallyUniformRealJacquetFamily_rankOne a
  | succ t ih =>
    let D := (nonempty_realQuotientMeasureData t a).some
    exact realGodementSpectralStep D a ih

/-- Pointwise holomorphic families agreeing on the strict real spectral chamber agree everywhere. -/
theorem eq_of_eqOn_realSpectralChamber {r : ℕ}
    {W V : (Fin (r + 1) → ℂ) → Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ∀ g, Differentiable ℂ (fun z => W z g))
    (hV : ∀ g, Differentiable ℂ (fun z => V z g))
    (hWV : ∀ z ∈ realSpectralChamber r, ∀ g, W z g = V z g) :
    W = V := by
  funext z g
  exact congrFun (Langlands.Analysis.eq_of_differentiable_eqOn_open (hW g) (hV g)
    (isOpen_realSpectralChamber r) (realSpectralChamber_nonempty r) (fun q hq => hWV q hq g)) z

end Langlands.Global.RankinSelbergGlobal.RealGodement
