import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks
import Langlands.Representation.GodementJacquet.MatrixTestTranslates
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-! Compact parameter integration of the actual Fourier and block orbits. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Topology

universe uX uY uF

section FiniteFamilies

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {Y : Type uY} [MeasurableSpace Y]

/-- Uniform local constancy and compact support turn integrable sections into
genuine joint integrability, by a finite sampled-value Schwartz expansion. -/
theorem integrable_compact_locallyConstant_family
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (η : Measure Y) [SFinite η]
    (H : X → Y → ℂ) (hlc : IsLocallyConstant H) (hc : HasCompactSupport H)
    (hi : ∀ x, Integrable (H x) η) :
    Integrable (fun z : X × Y => H z.1 z.2) (μ.prod η) := by
  obtain ⟨d, φ, r, he⟩ := exists_finite_schwartz_expansion H hlc hc
  have hsum : Integrable
      (fun z : X × Y => ∑ i : Fin d, φ i z.1 * H (r i) z.2) (μ.prod η) :=
    integrable_finsetSum _ fun i _ => ((φ i).integrable μ).mul_prod (hi (r i))
  exact hsum.congr (Filter.Eventually.of_forall fun z => (he z.2 z.1).symm)

end FiniteFamilies

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactOrbitTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance compactOrbitValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance compactOrbitLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance compactOrbitT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance compactOrbitSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance compactOrbitSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance compactOrbitMeasurable : MeasurableSpace F.Carrier := borel _
local instance compactOrbitBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance compactOrbitNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance compactOrbitNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance compactOrbitNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).isClosedEmbedding.locallyCompactSpace
local instance compactOrbitNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).secondCountableTopology
local instance compactOrbitTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The actual compact average of the Fourier-orbit kernel. -/
def compactSignedWeylOrbitFourierAverage
    (μ : Measure X) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (z : upperUnipotent (m + 2) F.Carrier × F.Carrier) : ℂ :=
  ∫ x, κ x * signedWeylOrbitFourierKernel ψ ν m (U x) Φ z ∂μ

/-- The actual compact average of the complementary-block kernel. -/
def compactSignedBlockOrbitAverage
    (μ : Measure X) (ψ : UnitaryAdditiveCharacter F.Carrier) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (κ : SchwartzBruhat X)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier))
    (z : upperUnipotent (m + 2) F.Carrier ×
      (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) : ℂ :=
  ∫ x, κ x * signedBlockOrbitKernel ψ m (U x) Φ z ∂μ

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
set_option maxHeartbeats 800000 in
private theorem locallyConstant_fourierOrbit_family
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    IsLocallyConstant (fun x => signedWeylOrbitFourierKernel ψ ν m (U x) Φ) := by
  let Φhat := rectangularFourierEquiv ψ ν (m + 2) (m + 2) hsd Φ
  have htr : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier =>
      rectangularFourierIntegral ψ ν Φ (Y * (U x).val)) := by
    simpa only [Φhat, rectangularFourierEquiv_apply, Units.val_one,
      Matrix.one_mul] using
      GodementJacquet.isLocallyConstant_matrixTranslate Φhat (fun _ : X => 1) U
        continuous_const hU
  unfold signedWeylOrbitFourierKernel
  exact htr.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier → ℂ)
      (z : upperUnipotent (m + 2) F.Carrier × F.Carrier) =>
    (inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
      T ((inverseTranspose (m + 2) F.Carrier z.1.val).val *
        (rankOneSignedWeyl (m + 1))⁻¹.val *
        Matrix.diagonal (Fin.cons z.2 (fun _ => 1))))

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
set_option maxHeartbeats 800000 in
private theorem locallyConstant_blockOrbit_family
    (ψ : UnitaryAdditiveCharacter F.Carrier) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    IsLocallyConstant (fun x => signedBlockOrbitKernel ψ m (U x) Φ) := by
  have htr := GodementJacquet.isLocallyConstant_matrixTranslate Φ
    (fun _ : X => 1) (fun x => inverseTranspose (m + 2) F.Carrier (U x))
    continuous_const ((continuous_inverseTranspose _ _).comp hU)
  have htr' : IsLocallyConstant (fun x => fun Y :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier =>
      Φ (Y * (inverseTranspose (m + 2) F.Carrier (U x)).val)) := by
    simpa only [Units.val_one, Matrix.one_mul] using htr
  unfold signedBlockOrbitKernel
  exact htr'.comp (fun (T : Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier → ℂ)
      (z : upperUnipotent (m + 2) F.Carrier ×
        (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) =>
    (inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
      T (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
        (rankOneSignedBlockWeyl (m + 1) (by omega)).val))

/-- One compact kernel integrates both sides of the same-test Weyl/block
identity. Norm one is required only where this kernel is nonzero. Both full
parameter products are integrable before their integrals are identified. -/
theorem compact_signedWeylOrbit_blockOrbit_fourier_duality
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      F.canonicalTopologicalData.determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (fun z : X × (upperUnipotent (m + 2) F.Carrier × F.Carrier) =>
      κ z.1 * signedWeylOrbitFourierKernel ψ ν m (U z.1) Φ z.2)
      (μ.prod ((unipotentHaar F.Carrier (m + 1)).prod ν.measure)) ∧
    Integrable (fun z : X × (upperUnipotent (m + 2) F.Carrier ×
        (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) =>
      κ z.1 * signedBlockOrbitKernel ψ m (U z.1) Φ z.2)
      (μ.prod ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)))) ∧
    (∫ z : X × (upperUnipotent (m + 2) F.Carrier × F.Carrier),
      κ z.1 * signedWeylOrbitFourierKernel ψ ν m (U z.1) Φ z.2
      ∂μ.prod ((unipotentHaar F.Carrier (m + 1)).prod ν.measure)) =
    ∫ z : X × (upperUnipotent (m + 2) F.Carrier ×
        (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)),
      κ z.1 * signedBlockOrbitKernel ψ m (U z.1) Φ z.2
      ∂μ.prod ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) := by
  have hlc := κ.locallyConstant.comp₂
    (locallyConstant_fourierOrbit_family F ψ ν hsd m U hU Φ)
    (fun c T => c • T)
  have hrc := κ.locallyConstant.comp₂
    (locallyConstant_blockOrbit_family F ψ m U hU Φ)
    (fun c T => c • T)
  have hlsec (x : X) : Integrable
      (fun z => κ x * signedWeylOrbitFourierKernel ψ ν m (U x) Φ z)
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure) := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
      exact integrable_zero _ _ _
    · exact (signedWeylOrbit_blockOrbit_fourier_duality F ψ ν hsd m
        (U x) (hunit x hx) Φ).1.const_mul (κ x)
  have hrsec (x : X) : Integrable
      (fun z => κ x * signedBlockOrbitKernel ψ m (U x) Φ z)
      ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
      exact integrable_zero _ _ _
    · exact (signedWeylOrbit_blockOrbit_fourier_duality F ψ ν hsd m
        (U x) (hunit x hx) Φ).2.1.const_mul (κ x)
  have hl0 := integrable_compact_locallyConstant_family μ _
    (fun x => κ x • signedWeylOrbitFourierKernel ψ ν m (U x) Φ)
    hlc κ.hasCompactSupport.smul_right hlsec
  have hr0 := integrable_compact_locallyConstant_family μ _
    (fun x => κ x • signedBlockOrbitKernel ψ m (U x) Φ)
    hrc κ.hasCompactSupport.smul_right hrsec
  have hl : Integrable (fun z : X × (upperUnipotent (m + 2) F.Carrier × F.Carrier) =>
      κ z.1 * signedWeylOrbitFourierKernel ψ ν m (U z.1) Φ z.2)
      (μ.prod ((unipotentHaar F.Carrier (m + 1)).prod ν.measure)) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hl0
  have hr : Integrable (fun z : X × (upperUnipotent (m + 2) F.Carrier ×
        (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) =>
      κ z.1 * signedBlockOrbitKernel ψ m (U z.1) Φ z.2)
      (μ.prod ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)))) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hr0
  refine ⟨hl, hr, ?_⟩
  rw [integral_prod _ hl, integral_prod _ hr]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : κ x = 0
  · simp only [hx, zero_mul, integral_zero]
  · simp only [integral_const_mul]
    rw [(signedWeylOrbit_blockOrbit_fourier_duality F ψ ν hsd m
      (U x) (hunit x hx) Φ).2.2]

/-- The compact parameter and unipotent integrations can be taken inside the
scalar and scalar/block integrations, with convergence on both sides. -/
theorem compact_signedWeylOrbit_blockOrbit_fourier_duality_averaged
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (U : X → Langlands.GeneralLinear (m + 2) F.Carrier) (hU : Continuous U)
    (κ : SchwartzBruhat X)
    (hunit : ∀ x, κ x ≠ 0 →
      F.canonicalTopologicalData.determinantNorm (m + 2) (U x) = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (fun a : F.Carrier => ∫ u,
      compactSignedWeylOrbitFourierAverage F μ ψ ν m U κ Φ (u, a) ∂unipotentHaar F.Carrier (m + 1)) ν.measure ∧
    Integrable (fun z : F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier =>
      ∫ u, compactSignedBlockOrbitAverage F μ ψ m U κ Φ (u, z) ∂unipotentHaar F.Carrier (m + 1))
      (ν.measure.prod (rectangularMeasure ν m 1)) ∧
    (∫ a : F.Carrier, ∫ u,
      compactSignedWeylOrbitFourierAverage F μ ψ ν m U κ Φ (u, a) ∂unipotentHaar F.Carrier (m + 1) ∂ν.measure) =
    ∫ a : F.Carrier, ∫ Z : Matrix (Fin m) (Fin 1) F.Carrier,
      ∫ u, compactSignedBlockOrbitAverage F μ ψ m U κ Φ (u, (a, Z)) ∂unipotentHaar F.Carrier (m + 1)
      ∂rectangularMeasure ν m 1 ∂ν.measure := by
  dsimp only [compactSignedWeylOrbitFourierAverage, compactSignedBlockOrbitAverage]
  obtain ⟨hl, hr, he⟩ := compact_signedWeylOrbit_blockOrbit_fourier_duality
    F μ ψ ν hsd m U hU κ hunit Φ
  have hl' := hl.integral_prod_right
  have hr' := hr.integral_prod_right
  refine ⟨hl'.integral_prod_right, hr'.integral_prod_right, ?_⟩
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr,
    integral_prod_symm _ hl', integral_prod_symm _ hr'] at he
  exact he.trans (integral_prod _ hr'.integral_prod_right)

end CanonicalPadic

end Langlands.RankinSelberg
