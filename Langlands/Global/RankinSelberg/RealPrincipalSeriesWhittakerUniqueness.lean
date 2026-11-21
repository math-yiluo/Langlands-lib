import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.Analysis.Local.NormalSubgroupModularCharacter
import Langlands.Analysis.SmoothOpenOrbitProportionality
import Langlands.Global.RankinSelberg.RealBorelAverageSurjectivity
import Langlands.Representation.Archimedean.LongestBruhatCell

/-! # Whittaker uniqueness for compact-derivative-bounded forms on real principal series -/

noncomputable section

open Function Set TopologicalSpace Topology MeasureTheory MeasureTheory.Measure
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean Langlands.Analysis.SmoothOpenOrbit
open scoped Distributions Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesWhittakerUniqueness

open RealBruhatDistributionRestriction RealWhittakerTranslationDistribution
open RealBorelTestAverage RealBorelRightHaar RealPrincipalSeriesDistribution
open RealBorelAverageSurjectivity RealJacquetFrobenius

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "H" => B × U
local notation "T" => Fin (r + 1) → ℝˣ
local notation "W" => weylLong (r + 1) ℝ
local notation "O" => longestBruhatCell ℝ r
local notation "TestC" => 𝓓(invertibleDomain r, ℂ)
local notation "TestR" => 𝓓(invertibleDomain r, ℝ)
local notation "μ" => rightBorelMeasure r

local instance : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
local instance : LocallyCompactSpace B := (isClosed_upperTriangularSubgroup (r + 1) ℝ).locallyCompactSpace
local instance : LocallyCompactSpace U := UpperUnipotent.locallyCompactSpace
local instance : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance : SecondCountableTopology G :=
  (show IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).isInducing.secondCountableTopology
local instance : SecondCountableTopology B :=
  (show IsInducing (Subtype.val : B → G) from IsInducing.subtypeVal).secondCountableTopology
local instance : SecondCountableTopology U :=
  (show IsInducing (Subtype.val : U → G) from IsInducing.subtypeVal).secondCountableTopology
local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩

/-- The Borel and upper unipotent group act by left and inverse right multiplication. -/
def matrixAction : H →* Module.End ℝ M where
  toFun p := (LinearMap.mulRight ℝ (p.2⁻¹).val.val).comp (LinearMap.mulLeft ℝ p.1.val.val)
  map_one' := LinearMap.ext fun X => by
    change (1 : M) * X * 1 = X
    rw [one_mul, mul_one]
  map_mul' p q := LinearMap.ext fun X => by
    change (p.1 * q.1).val.val * X * ((p.2 * q.2)⁻¹).val.val =
      p.1.val.val * (q.1.val.val * X * (q.2⁻¹).val.val) * (p.2⁻¹).val.val
    simp only [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, mul_assoc]

private theorem continuous_matrixAction :
    Continuous (fun p : H => LinearMap.toContinuousLinearMap (matrixAction p)) := by
  have h₁ : Continuous (fun p : H => p.1.val.val) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
  have h₂ : Continuous (fun p : H => (p.2⁻¹).val.val) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd.inv
  exact ((ContinuousLinearMap.mul ℝ M).flip.continuous.comp h₂).clm_comp
    ((ContinuousLinearMap.mul ℝ M).continuous.comp h₁)

private def reversalCoordinates : ((T × U) × U) ≃ₜ ((U × U) × T) where
  toFun z := ((z.1.2, z.2), fun i => z.1.1 i.rev)
  invFun z := ((fun i => z.2 i.rev, z.1.1), z.1.2)
  left_inv z := by simp only [Fin.rev_rev, Prod.mk.eta]
  right_inv z := by simp only [Fin.rev_rev, Prod.mk.eta]
  continuous_toFun :=
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_pi fun i => (continuous_apply i.rev).comp (continuous_fst.comp continuous_fst))
  continuous_invFun :=
    ((continuous_pi fun i => (continuous_apply i.rev).comp continuous_snd).prodMk
      (continuous_fst.comp continuous_fst)).prodMk (continuous_snd.comp continuous_fst)

/-- The reversal cell is a free open orbit of the Borel and upper unipotent group. -/
def orbitHomeomorph : H ≃ₜ (O : Set M) :=
  ((torusUnipotentHomeomorph (r := r)).symm.prodCongr (Homeomorph.refl U)).trans
    (reversalCoordinates.trans (longestBruhatCellChart ℝ r))

private theorem weylLong_mul_reversed_diagonal (d : T) :
    W * Iwasawa.diagonalUnits (fun i => d i.rev) = Iwasawa.diagonalUnits d * W := by
  rw [weylLong, permutation_mul_diagonalUnits]
  have he (i : Fin (r + 1)) : (Fin.revPerm⁻¹ i).rev = i := Fin.rev_rev i
  simp only [he]

theorem orbitHomeomorph_val (p : H) : (orbitHomeomorph p).val = matrixAction p (W).val := by
  obtain ⟨b, u⟩ := p
  let E := torusUnipotentHomeomorph (r := r)
  obtain ⟨⟨d, v⟩, rfl⟩ := E.surjective b
  have hv : E.symm (E (d, v)) = (d, v) := E.symm_apply_apply _
  change (longestBruhatCellChart ℝ r (reversalCoordinates (E.symm (E (d, v)), u))).val = _
  rw [hv]
  change (longestBruhatCellChart ℝ r ((v, u), fun i => d i.rev)).val =
    (E (d, v)).val.val * (W).val * (u⁻¹).val.val
  rw [longestBruhatCellChart_val, matrixUnipotentPair_smul_def, weylLong_mul_reversed_diagonal,
    torusUnipotentHomeomorph_val]
  simp only [Units.val_mul, mul_assoc]

private theorem longestCell_le : O ≤ invertibleDomain r := by
  rintro X ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

private instance : (μ).inv.IsHaarMeasure := by
  let : IsFiniteMeasureOnCompacts (μ).inv :=
    IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv B)
  let : (μ).inv.IsOpenPosMeasure :=
    (Homeomorph.inv B).continuous.isOpenPosMeasure_map (Homeomorph.inv B).surjective
  exact { map_mul_left_eq_self := map_mul_left_eq_self (μ).inv }

private theorem map_left_rightBorelMeasure (b : B) :
    Measure.map (b * ·) μ = modularCharacter b⁻¹ • μ := by
  simpa only [Measure.inv_inv] using Langlands.QuotientIntegration.map_mul_left_invHaar (μ).inv b

private theorem whittakerCharacter_mul (a : ℝˣ) (u v : U) :
    realWhittakerCharacter a (u * v).val = realWhittakerCharacter a u.val * realWhittakerCharacter a v.val := by
  simp only [realWhittakerCharacter, UpperUnipotent.mul_adjacent_entry, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul]

private theorem whittakerCharacter_one (a : ℝˣ) : realWhittakerCharacter a (1 : U).val = 1 := by
  have h (i : Fin r) : ((1 : U).val.val : M) i.castSucc i.succ = 0 :=
    Matrix.one_apply_ne (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  simp only [realWhittakerCharacter, h, Finset.sum_const_zero, AddChar.map_zero_eq_one]

private theorem continuous_whittakerCharacter (a : ℝˣ) :
    Continuous (fun u : U => realWhittakerCharacter a u.val) :=
  (realScaledCharacter a).continuous_complex.comp (continuous_finsetSum _ fun i _ =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i.castSucc i.succ)

variable (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2)
local notation "P" => principalSeries ℝ (r + 1) (posChar s e)
local notation "ds" => normalizedCharacterBlocks s e
local notation "χ" => positionBorelCharacter s e

private def borelFactor (b : B) : ℂ := (χ b : ℂ) * ((modularCharacter b⁻¹ : ℝ) : ℂ)

private def covarianceCharacter (a : ℝˣ) : H →* ℂ where
  toFun p := borelFactor s e p.1 * realWhittakerCharacter a (p.2⁻¹).val
  map_one' := by
    change borelFactor s e 1 * realWhittakerCharacter a ((1 : U)⁻¹).val = 1
    simp only [borelFactor, inv_one, map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
      whittakerCharacter_one, mul_one]
  map_mul' p q := by
    change borelFactor s e (p.1 * q.1) * realWhittakerCharacter a ((p.2 * q.2)⁻¹).val =
      (borelFactor s e p.1 * realWhittakerCharacter a (p.2⁻¹).val) *
        (borelFactor s e q.1 * realWhittakerCharacter a (q.2⁻¹).val)
    simp only [borelFactor, mul_inv_rev, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul,
      whittakerCharacter_mul]
    ring

private theorem continuous_covarianceCharacter (a : ℝˣ) : Continuous (covarianceCharacter s e a) := by
  change Continuous (fun p : H => borelFactor s e p.1 * realWhittakerCharacter a (p.2⁻¹).val)
  exact ((Units.continuous_val.comp ((continuous_positionBorelCharacter s e).comp continuous_fst)).mul
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (Langlands.Haar.continuous_modularCharacter_of_locallyCompact.comp continuous_fst.inv)))).mul
      ((continuous_whittakerCharacter a).comp continuous_snd.inv)

/-- The Whittaker equivariance law on the full real smooth principal series. -/
def IsWhittakerFunctional (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ) : Prop :=
  ∀ (u : U) (F : P), ℓ (RealPrincipalSeries.translate r ds u.val F) =
    realWhittakerCharacter a u.val * ℓ F

private theorem averageMap_pullback (p : H) (f g : TestC) (hg : ∀ X, g X = f (matrixAction p X)) :
    averageMap s e g = borelFactor s e p.1 •
      RealPrincipalSeries.translate r ds (p.2⁻¹).val (averageMap s e f) := by
  apply Subtype.ext
  funext x
  let y := x * (p.2⁻¹).val
  change borelAverage μ (inverseWeight χ) g x.val =
    borelFactor s e p.1 * borelAverage μ (inverseWeight χ) f y.val
  let F (b : B) := inverseWeight χ b * f (b.val.val * y.val)
  have hEq (b : B) : inverseWeight χ b * g (b.val.val * x.val) = (χ p.1 : ℂ) * F (p.1 * b) := by
    have hχ : inverseWeight χ b = (χ p.1 : ℂ) * inverseWeight χ (p.1 * b) :=
      congrArg Units.val (show (χ b)⁻¹ = χ p.1 * (χ (p.1 * b))⁻¹ by
        rw [map_mul, mul_comm (χ p.1) (χ b), mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul])
    rw [hg, hχ]
    change (χ p.1 : ℂ) * inverseWeight χ (p.1 * b) *
      f (p.1.val.val * (b.val.val * x.val) * (p.2⁻¹).val.val) = _
    simp only [F, y, Subgroup.coe_mul, Units.val_mul, mul_assoc]
  change (∫ b : B, inverseWeight χ b * g (b.val.val * x.val) ∂μ) =
    borelFactor s e p.1 * ∫ b : B, F b ∂μ
  simp only [hEq]
  rw [integral_const_mul, ← (measurableEmbedding_mulLeft p.1).integral_map,
    map_left_rightBorelMeasure, integral_smul_nnreal_measure]
  change (χ p.1 : ℂ) * ((modularCharacter p.1⁻¹ : ℝ) • ∫ b, F b ∂μ) = _
  rw [Complex.real_smul, borelFactor, mul_assoc]

private theorem averagedFunctional_covariant (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ)
    (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) (hψ : IsWhittakerFunctional s e a ℓ) :
    IsCovariant matrixAction (covarianceCharacter s e a) (averagedFunctional s e ℓ hb) := by
  intro p f g hg
  change ℓ (averageMap s e g) =
    (borelFactor s e p.1 * realWhittakerCharacter a (p.2⁻¹).val) * ℓ (averageMap s e f)
  rw [averageMap_pullback s e p f g hg, map_smul, smul_eq_mul, hψ (p.2⁻¹), mul_assoc]

private def extendCellTest : 𝓓(O, ℂ) →L[ℂ] TestC := TestFunction.monoCLM ℂ

private theorem extendCellTest_apply (f : 𝓓(O, ℂ)) (X : M) : extendCellTest f X = f X := by
  have h : ((extendCellTest f : TestC) : M → ℂ) = f := by
    simp [extendCellTest, longestCell_le (r := r)]
  exact congrFun h X

private def cellFunctional (ℓ : P →ₗ[ℂ] ℂ) (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) :
    𝓓(O, ℂ) →L[ℂ] ℂ :=
  (averagedFunctional s e ℓ hb).comp extendCellTest

private theorem cellFunctional_covariant (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ)
    (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) (hψ : IsWhittakerFunctional s e a ℓ) :
    IsCovariant matrixAction (covarianceCharacter s e a) (cellFunctional s e ℓ hb) := by
  intro p f g hg
  exact averagedFunctional_covariant s e a ℓ hb hψ p (extendCellTest f) (extendCellTest g) (fun X => by
    rw [extendCellTest_apply, extendCellTest_apply, hg])

private theorem cellFunctional_realTest (ℓ : P →ₗ[ℂ] ℂ)
    (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ)
    (f : TestR) (hf : tsupport f ⊆ reversalCellImage r) :
    cellFunctional s e ℓ hb (TestFunction.postcompCLM Complex.ofRealCLM
      (⟨f, f.contDiff, f.hasCompactSupport, hf⟩ : 𝓓(O, ℝ))) =
      averagedDistribution s e ℓ hb f := by
  rw [averagedDistribution_apply]
  change ℓ (averageMap s e (extendCellTest _)) = _
  apply congrArg ℓ
  apply congrArg (averageMap s e)
  ext X
  rw [extendCellTest_apply]
  rfl

private theorem hasCompactDerivativeBound_smul (ℓ : P →ₗ[ℂ] ℂ)
    (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) (c : ℂ) :
    RealPrincipalSeries.HasCompactDerivativeBound r ds (c • ℓ) := by
  obtain ⟨m, Xs, A, hA, hB⟩ := hb
  refine ⟨m, Xs, ‖c‖ * A, mul_nonneg (norm_nonneg _) hA, fun f b hf => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB f b hf) (norm_nonneg _)

private theorem cellFunctional_ne_zero (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ)
    (hb : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) (hψ : IsWhittakerFunctional s e a ℓ)
    (hℓ : ℓ ≠ 0) : cellFunctional s e ℓ hb ≠ 0 := by
  intro h
  have hv : Distribution.IsVanishingOn (averagedDistribution s e ℓ hb) (reversalCellImage r) := by
    intro f hf
    rw [← cellFunctional_realTest s e ℓ hb f hf, h]
    rfl
  have hD := eq_zero_of_unipotent_covariance_of_reversalCell_vanishing _ a
    (averagedDistribution_covariant s e a ℓ hb hψ) hv
  have hb₀ : RealPrincipalSeries.HasCompactDerivativeBound r ds (0 : P →ₗ[ℂ] ℂ) := by
    simpa only [zero_smul] using hasCompactDerivativeBound_smul s e ℓ hb 0
  apply hℓ
  apply eq_of_averagedDistribution_eq s e ℓ 0 hb hb₀
  rw [hD]
  ext1 f
  rfl

/-- A nonzero bounded Whittaker functional on the real character principal
series determines every bounded functional with the same character up to scalar. -/
theorem exists_smul_of_whittakerFunctional (a : ℝˣ) (ℓ₁ ℓ₂ : P →ₗ[ℂ] ℂ)
    (hb₁ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ₁)
    (hb₂ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ₂)
    (hψ₁ : IsWhittakerFunctional s e a ℓ₁) (hψ₂ : IsWhittakerFunctional s e a ℓ₂)
    (hℓ₁ : ℓ₁ ≠ 0) : ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  obtain ⟨c, hc⟩ := exists_proportional_of_covariance matrixAction orbitHomeomorph (W).val
    orbitHomeomorph_val (Measure.haar : Measure H) continuous_matrixAction
    (covarianceCharacter s e a) (continuous_covarianceCharacter s e a)
    (cellFunctional s e ℓ₁ hb₁) (cellFunctional s e ℓ₂ hb₂)
    (cellFunctional_covariant s e a ℓ₁ hb₁ hψ₁) (cellFunctional_covariant s e a ℓ₂ hb₂ hψ₂)
    (cellFunctional_ne_zero s e a ℓ₁ hb₁ hψ₁ hℓ₁)
  let D₁ := averagedDistribution s e ℓ₁ hb₁
  let D₂ := averagedDistribution s e ℓ₂ hb₂
  let D : 𝓓'(invertibleDomain r, ℂ) := D₂ - c • D₁
  have hD₁ : IsUnipotentWhittakerCovariant D₁ a := averagedDistribution_covariant s e a ℓ₁ hb₁ hψ₁
  have hD₂ : IsUnipotentWhittakerCovariant D₂ a := averagedDistribution_covariant s e a ℓ₂ hb₂ hψ₂
  have hCov : IsUnipotentWhittakerCovariant D a := by
    constructor
    · intro u f
      change D₂ (leftTranslateTest u.val f) - c * D₁ (leftTranslateTest u.val f) = D₂ f - c * D₁ f
      rw [hD₂.1, hD₁.1]
    · intro u f
      change D₂ (rightTranslateTest u.val f) - c * D₁ (rightTranslateTest u.val f) =
        realWhittakerCharacter a u.val * (D₂ f - c * D₁ f)
      rw [hD₂.2, hD₁.2]
      ring
  have hv : Distribution.IsVanishingOn D (reversalCellImage r) := by
    intro f hf
    have h := hc (TestFunction.postcompCLM Complex.ofRealCLM
      (⟨f, f.contDiff, f.hasCompactSupport, hf⟩ : 𝓓(O, ℝ)))
    rw [cellFunctional_realTest s e ℓ₂ hb₂ f hf, cellFunctional_realTest s e ℓ₁ hb₁ f hf] at h
    exact sub_eq_zero.mpr h
  have hd : D₂ = c • D₁ := sub_eq_zero.mp
    (eq_zero_of_unipotent_covariance_of_reversalCell_vanishing D a hCov hv)
  let hb := hasCompactDerivativeBound_smul s e ℓ₁ hb₁ c
  have hscale : averagedDistribution s e (c • ℓ₁) hb = c • D₁ := by
    ext1 f
    rfl
  exact ⟨c, eq_of_averagedDistribution_eq s e ℓ₂ (c • ℓ₁) hb₂ hb (hd.trans hscale.symm)⟩

/-- Whittaker uniqueness for compact-derivative-bounded functionals on the
full normalized real character principal series. -/
def RealPrincipalSeriesWhittakerUniquenessStatement : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) (a : ℝˣ)
    (ℓ₁ ℓ₂ : principalSeries ℝ (r + 1) (posChar s e) →ₗ[ℂ] ℂ),
    RealPrincipalSeries.HasCompactDerivativeBound r (normalizedCharacterBlocks s e) ℓ₁ →
    RealPrincipalSeries.HasCompactDerivativeBound r (normalizedCharacterBlocks s e) ℓ₂ →
    IsWhittakerFunctional s e a ℓ₁ → IsWhittakerFunctional s e a ℓ₂ → ℓ₁ ≠ 0 →
    ∃ c : ℂ, ℓ₂ = c • ℓ₁

theorem realPrincipalSeriesWhittakerUniqueness : RealPrincipalSeriesWhittakerUniquenessStatement :=
  fun _ => exists_smul_of_whittakerFunctional

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesWhittakerUniqueness
