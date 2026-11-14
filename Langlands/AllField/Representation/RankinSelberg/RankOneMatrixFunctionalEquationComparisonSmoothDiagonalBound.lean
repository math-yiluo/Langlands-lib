import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound
/-! Genuine diagonal-torus bounds from ambient matrix convergence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement biSmooth_matrixDiagonal_convergesOnRight integrable_biSmooth_matrixDiagonalIntegrand integrable_diagonalUnits_of_principalFixed matrixDiagonalIntegrand matrixIntegrand_exists_principalFixed measurable_biSmooth_matrixIntegrand measure_diagonalUnits_preimage_principalLevel_le_one normalizedAbsoluteValue normalizedAbsoluteValue_apply smoothDiagonalGLBorel smoothDiagonalGLLocallyCompact smoothDiagonalGLMeasurable smoothDiagonalGLSecondCountable smoothDiagonalLocalField smoothDiagonalSecondCountable smoothDiagonalT2 smoothDiagonalTopology smoothDiagonalUnitsBorel smoothDiagonalUnitsMeasurable smoothDiagonalUnitsSecondCountable smoothDiagonalValuativeRel smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear
open Langlands.Conductor
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped ENNReal NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance smoothDiagonalT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance smoothDiagonalSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance smoothDiagonalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance smoothDiagonalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance smoothDiagonalGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance smoothDiagonalGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

local instance smoothDiagonalUnitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance smoothDiagonalUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance smoothDiagonalUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩

/-- The inverse image of an actual principal subgroup under the full diagonal
homomorphism has finite product multiplicative Haar measure. -/
theorem measure_diagonalUnits_preimage_principalLevel_le_one (n a : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F)
      (Iwasawa.diagonalUnits ⁻¹' (principalLevelSubgroup F n a : Set _)) ≤ 1 := by
  let U : Set (Fin (n + 1) → Fˣ) := Set.univ.pi fun _ =>
    (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ)
  have hsub : Iwasawa.diagonalUnits ⁻¹'
      (principalLevelSubgroup F n a : Set _) ⊆ U := by
    intro x hx i hi
    have hInt := principalLevelSubgroup_antitone F n (Nat.zero_le a) hx
    rw [principalLevelSubgroup_zero] at hInt
    have hentries := (mem_integralSubgroup (ValuativeRel.valuation F).integer n _).1 hInt
    apply (mem_integralUnits _ _).2
    constructor
    · simpa only [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq] using hentries.1 i i
    · simpa only [← map_inv, Iwasawa.diagonalUnits_val, Pi.inv_apply,
        Matrix.diagonal_apply_eq] using hentries.2 i i
  calc
    _ ≤ (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) U :=
      measure_mono hsub
    _ = 1 := by
      rw [Measure.pi_pi]
      simp only [localMultiplicativeHaar_integerUnits, Finset.prod_const_one]

/-- The actual full diagonal-torus integral inherits ambient integrability
for every measurable right-principal-fixed complex function. -/
theorem integrable_diagonalUnits_of_principalFixed (n a : ℕ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Measurable f)
    (hfixed : ∀ k ∈ principalLevelSubgroup F n a, ∀ g, f (g * k) = f g)
    (hi : Integrable f (generalLinearHaar F n)) :
    Integrable (fun x : Fin (n + 1) → Fˣ => f (Iwasawa.diagonalUnits x))
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
  have hKpos : generalLinearHaar F n (principalLevelSubgroup F n a : Set _) ≠ 0 :=
    ((principalLevelOpenSubgroup F n a).isOpen.measure_pos _
      ⟨1, one_mem _⟩).ne'
  have hpre := (measure_diagonalUnits_preimage_principalLevel_le_one F n a).trans_lt
    ENNReal.one_lt_top
  have : SigmaFinite (localMultiplicativeHaar F) := inferInstance
  have : SigmaFinite (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) :=
    inferInstance
  exact integrable_subgroup_of_right_invariant (generalLinearHaar F n)
    (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F)
    Iwasawa.diagonalUnits (continuous_diagonalUnits (n + 1)).measurable
    (principalLevelSubgroup F n a)
    (principalLevelOpenSubgroup F n a).isOpen.measurableSet hKpos hpre.ne f hf hfixed hi

/-- The literal full-matrix integrand restricted to the full diagonal torus. -/
def matrixDiagonalIntegrand {n : ℕ} (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (a : Fin (n + 1) → Fˣ) : ℂ :=
  matrixIntegrand abv Φ s f (Iwasawa.diagonalUnits a)

/-- A genuinely convergent bi-smooth matrix integrand is integrable on the
full diagonal torus for its actual product multiplicative Haar measure. -/
theorem integrable_biSmooth_matrixDiagonalIntegrand
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients σ) (s : ℂ)
    (hi : Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s f.val) :
    Integrable (matrixDiagonalIntegrand F Φ s f.val)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
  obtain ⟨a, ha, hfixed⟩ := matrixIntegrand_exists_principalFixed F σ Φ f
  exact integrable_diagonalUnits_of_principalFixed F n a _
    (measurable_biSmooth_matrixIntegrand F σ Φ f s) (hfixed s) hi

/-- The same common shifted matrix half-plane works for all the actual
full diagonal restrictions, without any uniformizer choice. -/
theorem biSmooth_matrixDiagonal_convergesOnRight
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F σ) :
    ∃ b : ℝ, ∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
      ∀ s : ℂ, b < s.re →
      Integrable (matrixDiagonalIntegrand F Φ (s + jpssShift n) f.val)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
  obtain ⟨b, hb⟩ := hMatrix
  exact ⟨b, fun Φ f s hs =>
    integrable_biSmooth_matrixDiagonalIntegrand F σ Φ f (s + jpssShift n) (hb Φ f s hs)⟩

end Langlands.AllField.RankinSelberg
