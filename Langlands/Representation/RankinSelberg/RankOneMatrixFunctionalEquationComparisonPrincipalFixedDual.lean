import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalModelDual

/-! Removing the same principal parameter for a genuinely principal-fixed function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped NNReal ENNReal

namespace Langlands.Conductor

open GeneralLinear
universe uK
variable {K : Type uK} [Field K]

/-- The actual principal congruence subgroup is preserved by inverse transpose,
including level zero. -/
theorem inverseTranspose_mem_principalCongruenceSubgroup
    (O : Subring K) (n : ℕ) (I : Ideal O)
    {k : Langlands.GeneralLinear (n + 1) K}
    (hk : k ∈ principalCongruenceSubgroup O n I) :
    inverseTranspose (n + 1) K k ∈ principalCongruenceSubgroup O n I := by
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  have hi : inverseTranspose (n + 1) O k₀ ∈ integralPrincipalCongruence n I := by
    apply (mem_integralPrincipalCongruence n I _).2
    intro i j
    have h := (mem_integralPrincipalCongruence n I k₀⁻¹).1
      ((integralPrincipalCongruence n I).inv_mem hk₀) j i
    simpa only [inverseTranspose_entry, Matrix.one_apply, eq_comm] using h
  refine ⟨inverseTranspose (n + 1) O k₀, hi, ?_⟩
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, inverseTranspose_entry,
    ← MonoidHom.map_inv]

/-- Every actual principal level, with its existing integer ring, is stable
under the inverse-transpose automorphism. -/
theorem inverseTranspose_mem_principalLevelSubgroup
    (K : Type uK) [Field K] [ValuativeRel K] (n a : ℕ)
    {k : Langlands.GeneralLinear (n + 1) K}
    (hk : k ∈ principalLevelSubgroup K n a) :
    inverseTranspose (n + 1) K k ∈ principalLevelSubgroup K n a :=
  inverseTranspose_mem_principalCongruenceSubgroup _ _ _ hk

end Langlands.Conductor

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Induction Topology Conductor
open RankOneIwasawa RankOneBox CompactWhittakerSynthesis CompactWhittakerApproximation

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalFixedDualTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalFixedDualValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalFixedDualLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalFixedDualT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalFixedDualSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance principalFixedDualMeasurable : MeasurableSpace F.Carrier := borel _
local instance principalFixedDualBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance principalFixedDualNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance principalFixedDualNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalFixedDualNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance principalFixedDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalFixedDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalFixedDualGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance principalFixedDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance principalFixedDualNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance principalFixedDualTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance principalFixedDualUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance principalFixedDualUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance principalFixedDualUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The unaveraged actual signed complementary block, at the same exponent. -/
def principalFixedBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) : ℂ :=
  determinantWeight abv z.1 s *
    W (AdjacentBlockReduction.blockMatrixAt m 0 (by omega) z.1 z.2 *
      rankOneSignedBlockWeyl (m + 1) (by omega))

/-- A principal-fixed function loses no information in the full principal
parameter: its true weighted integrand is almost everywhere constant in it. -/
theorem principalModelBlockIntegrand_ae_of_fixed
    (ν : AdditiveHaarMeasure F.Carrier) (m a : ℕ) (C : ℝ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g, W (g * k) = W g) :
    principalModelBlockIntegrand F m s W
      =ᵐ[(principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))]
      (fun z => principalFixedBlockIntegrand F m s W z.2) := by
  have hk := (Measure.quasiMeasurePreserving_fst
    (μ := principalAveragingMeasure F (n := m + 1) a C)
    (ν := (glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))).ae
    (principalAveragingMeasure_ae_mem F a C)
  filter_upwards [hk] with z hz
  unfold principalModelBlockIntegrand principalSignedBlockPoint principalFixedBlockIntegrand
  rw [hW _ (inverseTranspose_mem_principalLevelSubgroup F.Carrier (m + 1) a hz)]

/-- Genuine scalar/block convergence implies convergence on the full product
with the same principal averaging parameter, before taking its average. -/
theorem integrable_principalModelBlockIntegrand_of_fixed
    (ν : AdditiveHaarMeasure F.Carrier) (m a : ℕ) (C : ℝ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g, W (g * k) = W g)
    (hi : Integrable (principalFixedBlockIntegrand F m s W)
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) :
    Integrable (principalModelBlockIntegrand F m s W)
      ((principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := by
  have h := (integrable_const (1 : ℂ)
    (μ := principalAveragingMeasure F (n := m + 1) a C)).mul_prod hi
  simp only [one_mul] at h
  exact h.congr (principalModelBlockIntegrand_ae_of_fixed F ν m a C s W hW).symm

/-- The original principal mass is exactly the scalar relating the fixed
block integral to the full product integral. -/
theorem integral_principalModelBlockIntegrand_of_fixed
    (ν : AdditiveHaarMeasure F.Carrier) (m a : ℕ) {C : ℝ} (hC : 0 ≤ C) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g, W (g * k) = W g) :
    (∫ z, principalModelBlockIntegrand F m s W z
      ∂(principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) =
    (C : ℂ) * ∫ z, principalFixedBlockIntegrand F m s W z
      ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
  rw [integral_congr_ae (principalModelBlockIntegrand_ae_of_fixed F ν m a C s W hW)]
  calc
    _ = (∫ _k, (1 : ℂ) ∂principalAveragingMeasure F (n := m + 1) a C) *
        ∫ z, principalFixedBlockIntegrand F m s W z
          ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
      simpa only [one_mul] using integral_prod_mul
        (fun _k : Langlands.GeneralLinear (m + 2) F.Carrier => (1 : ℂ))
        (principalFixedBlockIntegrand F m s W)
    _ = _ := by
      simp [integral_const, measureReal_def, principalAveragingMeasure_mass F a hC,
        ENNReal.toReal_ofReal hC, Complex.real_smul]


/-- For an actual principal-fixed coefficient-model vector, the same original
box constant multiplies the actual signed block integral. Scalar/block
convergence supplies the full product bound needed by model approximation. -/
theorem principalFixedModelDual_pairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (f : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ)
    (hfixed : ∀ k ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ f (g * k) = glModelFunction ψ (m + 1) σ ℓ f g)
    (hi : Integrable (principalModelFourierIntegrand F ψ ν m a s
        (glModelFunction ψ (m + 1) σ ℓ f)) (generalLinearHaar F.Carrier (m + 1)))
    (hj : Integrable (principalFixedBlockIntegrand F m s
        (glModelFunction ψ (m + 1) σ ℓ f))
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s
      (glModelFunction ψ (m + 1) σ ℓ f) h ∂generalLinearHaar F.Carrier (m + 1)) =
    (boxExtractionConstant F (n := m + 1)
      (F.canonicalTopologicalData.additiveConductor ψ + a)
      (F.canonicalTopologicalData.additiveConductor ψ) a : ℂ) *
      ∫ z, principalFixedBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ f) z
        ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
  let C := boxExtractionConstant F (n := m + 1)
    (F.canonicalTopologicalData.additiveConductor ψ + a)
    (F.canonicalTopologicalData.additiveConductor ψ) a
  have hC : 0 ≤ C := (boxExtractionConstant_pos F (n := m + 1) hA ha).le
  have hraw := integrable_principalModelBlockIntegrand_of_fixed F ν m a C s
    (glModelFunction ψ (m + 1) σ ℓ f) hfixed hj
  exact (principalModelDual_pairing F ψ ν hsd ha hA σ hσ ℓ f s hi hraw).trans
    (integral_principalModelBlockIntegrand_of_fixed F ν m a hC s
      (glModelFunction ψ (m + 1) σ ℓ f) hfixed)

end Langlands.RankinSelberg
