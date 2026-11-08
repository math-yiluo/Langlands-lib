import Langlands.Representation.RankinSelberg.HighlyRamified.CoreTestData
import Langlands.Representation.RankinSelberg.HighlyRamified.TwistedSmearModel
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType

/-!
# Model vectors and analytic inputs of the adjacent-rank step

* `exists_candidateTest_model`: the candidate test function `χ(det y) Σ_z Φ(z) W(y w n(z))` is a
  model vector of the twisted candidate `π ⊗ χ ∘ det` for the same functional.
* `integralFourier_dualWeight_inPow`: the restricted Fourier transform of `Φ₂` is supported on
  `(𝔭^f)^(m+1)` once `c ≥ 2f`.
* `integral_integralFourier_eq`: the smeared dual function at `[[A,0],[x,1]]` integrated against
  `S₂(rev x)` is `χ(det A)` times the twisted smeared function at `diag(A,1)`.
* `dualShellConstant_ne_zero`, `shellConstant_ne_zero`: the constants of the shell identities
  do not vanish.
* `dual_integrand_measurable_integrable`: the dual corank-one integrand of model vectors is
  measurable, and integrable on a right half-plane.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF uV uW

section Model

variable {F : Type uF} [Field F] [TopologicalSpace F] {m : ℕ}

/-- The candidate test function is a model vector of the twisted candidate. -/
theorem exists_candidateTest_model (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (m + 2 + 1) F) V)
    (ℓ : glFunctionals ψ (m + 2) π) (w : (coefficientModel π ℓ).toSubmodule)
    (T : Finset (Fin (m + 2) → F)) (Φ : (Fin (m + 2) → F) → ℂ) :
    ∃ ℓχ : glFunctionals ψ (m + 2) (Langlands.twist (χ.comp determinant) π),
      ℓχ.val = ℓ.val ∧
      ∃ fc : (coefficientModel (Langlands.twist (χ.comp determinant) π) ℓχ).toSubmodule,
        fc.val.val = candidateTest ψ χ w.val T Φ := by
  obtain ⟨v, hv⟩ := modelMap_surjective π ℓ w
  have hw : ∀ g, w.val.val g = ℓ.val (π g v) := fun g => by rw [← hv]; rfl
  set v' : V := ∑ z ∈ T, Φ z • π (weylLong (m + 3) F * firstRowUnipotent z) v with hv'
  refine ⟨twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ, rfl,
    twistModelLinearMap _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ
      (modelMap π ℓ v'), ?_⟩
  funext g
  change (χ (determinant g) : ℂ) * ℓ.val (π g v') = _
  unfold candidateTest
  congr 1
  rw [hv', map_sum, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, hw, ← Module.End.mul_apply, ← map_mul, mul_assoc]

end Model

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coreModelFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coreModelValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance coreModelLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance coreModelFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance coreModelFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance coreModelGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance coreModelGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreModelUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance coreModelUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreModelQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance coreModelQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {m : ℕ}

/-- The restricted Fourier transform of `Φ₂` is supported on `(𝔭^f)^(m+1)`. -/
theorem integralFourier_dualWeight_inPow (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (η : AdditiveHaarMeasure F.Carrier)
    {ω : F.Carrierˣ →* ℂˣ} {f c : ℕ} (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    {ϖ : F.Carrier} (hϖ0 : ϖ ≠ 0) (hϖ : InPow 1 ϖ) (hc : f + f ≤ c)
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hTK : (T : Set (Fin (m + 1) → F.Carrier)) ⊆ scaledLattice F ϖ c m)
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ v ∈ scaledLattice F ϖ c m, ∃ t ∈ T, v - t ∈ integerLattice F m)
    (v : Fin (m + 1) → F.Carrier) (hv : integralFourier ψ T (dualWeight ω ϖ c f) v ≠ 0) :
    ∀ k, InPow f (v k) := by
  classical
  unfold integralFourier at hv
  split_ifs at hv with hint
  · by_contra hnot
    exact hv (dualWeight_fourier_eq_zero F ψ hψ η hf hω hϖ0 hϖ hc T hTK hT hcov v hint hnot)
  · exact absurd rfl hv

/-- The smeared dual function integrated against `S₂(rev x)` at `[[A,0],[x,1]]` is `χ(det A)`
times the twisted smeared function at `diag(A,1)`. -/
theorem integral_integralFourier_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (η : AdditiveHaarMeasure F.Carrier) (χ ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrier) (c f : ℕ)
    (T : Finset (Fin (m + 1) → F.Carrier)) (f' : InverseWhittakerFunctions ψ (m + 1))
    (A : Langlands.GeneralLinear (m + 1) F.Carrier) :
    ∫ x, integralFourier ψ T (dualWeight ω ϖ c f) (fun k => x 0 k.rev) *
        (secondDualFunction ψ (m + 1) f').val
          (lowerBlockPair A x 1 : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
        ∂rectangularMeasure η 1 (m + 1) =
      (χ (determinant A) : ℂ) * twistedSmear F ψ η χ ω ϖ c f T f' (rankInclusion 1 A) := by
  classical
  have hdet : determinant (rankInclusion 1 A) = determinant A :=
    Units.ext (LastRowReduction.rankInclusion_det A)
  unfold twistedSmear
  rw [hdet, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  congr 1
  funext x
  rw [lowerBlockPair_one_eq_mul_lowerRow]
  congr 1

/-- The constant of the dual shell integral does not vanish. -/
theorem dualShellConstant_ne_zero (η : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    (ϖ : F.Carrierˣ) (c : ℕ) {κ₁ ωτ : ℂ} (hκ : κ₁ ≠ 0) (hωτ : ωτ ≠ 0) (s : ℂ) :
    dualShellConstant F η χ ϖ c m κ₁ ωτ s ≠ 0 := by
  have hOfin : η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier) < ⊤ :=
    (isCompact_integer F).measure_lt_top
  have hOpos : 0 < η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measure_pos _
      ⟨0, Subring.zero_mem _⟩
  have hvol : ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
      Set F.Carrier)).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hdw : RankinSelberg.determinantWeight abv
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹) (s - 1 / 2) ≠ 0 := by
    unfold RankinSelberg.determinantWeight
    rw [Complex.cpow_ne_zero_iff]
    left
    have hpos := AbsoluteValue.pos abv
      (determinant (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)).ne_zero
    exact_mod_cast hpos.ne'
  unfold dualShellConstant
  have h1 : ((χ (determinant (weylLong (m + 1 + 1) F.Carrier)) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Units.ne_zero _)
  have h2 : ((χ ((ϖ ^ c)⁻¹) : ℂ)) ^ (m + 1) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2)
    (pow_ne_zero _ hvol)) hκ) hωτ) hdw

/-- The constant of the `j = 0` shell identity does not vanish. -/
theorem shellConstant_ne_zero (η : AdditiveHaarMeasure F.Carrier) (χ ω : F.Carrierˣ →* ℂˣ)
    (ϖ : F.Carrierˣ) (c f : ℕ) {κ₁ : ℂ} (hκ : κ₁ ≠ 0) (C : (F.Carrierˣ →* ℂˣ) → ℂˣ)
    (ωπ : F.Carrierˣ →* ℂˣ) :
    shellConstant F η χ ω ϖ c f m κ₁ C ωπ ≠ 0 := by
  unfold shellConstant
  have hq : (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    have := F.canonicalTopologicalData.residueCardinality_gt_one
    exact_mod_cast (show F.canonicalTopologicalData.residueCardinality ≠ 0 by omega)
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Units.ne_zero _)))
    (inv_ne_zero (Units.ne_zero _))) (mul_ne_zero (mul_ne_zero
      (dualShellConstant_ne_zero F η χ ϖ c hκ (Units.ne_zero _) 0) (inv_ne_zero (Units.ne_zero _)))
      (firstColumnVolume_ne_zero F))) (zpow_ne_zero _ hq)

/-- The dual corank-one integrand of model vectors of generic representations is measurable,
and integrable on a right half-plane. -/
theorem dual_integrand_measurable_integrable (ψ : UnitaryAdditiveCharacter F.Carrier)
    (η : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {Pi : Representation ℂ (Langlands.GeneralLinear (m + 2 + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) W}
    (hPi : IsGeneric ψ (m + 2) Pi) (hσ : IsGeneric ψ (m + 1) σ)
    (ℓ : glFunctionals ψ (m + 2) Pi) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glInverseFunctionals ψ (m + 1) σ) (hℓ' : ℓ'.val ≠ 0)
    (fc : (coefficientModel Pi ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Measurable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) fc.val)
        (secondDualFunction ψ (m + 1) f'.val) s) ∧
      Integrable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) fc.val)
        (secondDualFunction ψ (m + 1) f'.val) s) (unipotentQuotientHaar F.Carrier (m + 1)) := by
  have hPi' := isOfWhittakerType_firstDual ψ Pi (isOfWhittakerType_of_isGeneric F hPi)
  have hσ' := isOfWhittakerType_secondDual ψ σ (isOfInverseWhittakerType_of_isGeneric F hσ)
  obtain ⟨a, ha⟩ := corankOne_integrable_of_whittakerType F (ψ.scale (-1)) η hPi' hσ'
    (firstDualFunctional ψ Pi ℓ) (firstDualFunctional_ne_zero ψ Pi hℓ)
    (secondDualFunctional ψ σ ℓ') (secondDualFunctional_ne_zero ψ σ hℓ')
    (firstDualModelMap ψ Pi ℓ fc) (secondDualModelMap ψ σ ℓ' f')
  obtain ⟨L₁, hL₁⟩ := model_rightInvariant (inverseTransposePullback_isSmooth Pi hPi.2.1.1)
    (firstDualFunctional ψ Pi ℓ) (firstDualModelMap ψ Pi ℓ fc)
  obtain ⟨L₂, hL₂⟩ := model_rightInvariant (inverseTransposePullback_isSmooth σ hσ.2.1.1)
    (secondDualFunctional ψ σ ℓ') (secondDualModelMap ψ σ ℓ' f')
  exact ⟨a, fun s hs => ⟨measurable_corankOneIntegrand F (ψ.scale (-1)) _ _ L₁ hL₁ L₂ hL₂ s,
    ha s hs⟩⟩

end Canonical

end Langlands.RankinSelberg.HighlyRamified
