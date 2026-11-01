import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound
import Mathlib.Topology.Algebra.IsOpenUnits

/-! Genuine diagonal-torus bounds from ambient matrix convergence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Topology Conductor GodementJacquet HarmonicAnalysis
open scoped ENNReal NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance smoothDiagonalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance smoothDiagonalValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance smoothDiagonalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance smoothDiagonalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance smoothDiagonalSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance smoothDiagonalMeasurable : MeasurableSpace F.Carrier := borel _
local instance smoothDiagonalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance smoothDiagonalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance smoothDiagonalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance smoothDiagonalGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance smoothDiagonalGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData


local instance smoothDiagonalUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance smoothDiagonalUnitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace
local instance smoothDiagonalUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance smoothDiagonalUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

/-- The inverse image of an actual principal subgroup under the full diagonal
homomorphism has finite product multiplicative Haar measure. -/
theorem measure_diagonalUnits_preimage_principalLevel_le_one (n a : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
      (Iwasawa.diagonalUnits ⁻¹' (principalLevelSubgroup F.Carrier n a : Set _)) ≤ 1 := by
  let U : Set (Fin (n + 1) → F.Carrierˣ) := Set.univ.pi fun _ =>
    (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
  have hsub : Iwasawa.diagonalUnits ⁻¹'
      (principalLevelSubgroup F.Carrier n a : Set _) ⊆ U := by
    intro x hx i hi
    have hInt := principalLevelSubgroup_antitone F.Carrier n (Nat.zero_le a) hx
    rw [principalLevelSubgroup_zero] at hInt
    have hentries := (mem_integralSubgroup (ValuativeRel.valuation F.Carrier).integer n _).1 hInt
    apply (mem_integralUnits _ _).2
    constructor
    · simpa only [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq] using hentries.1 i i
    · simpa only [← map_inv, Iwasawa.diagonalUnits_val, Pi.inv_apply,
        Matrix.diagonal_apply_eq] using hentries.2 i i
  calc
    _ ≤ (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) U :=
      measure_mono hsub
    _ = 1 := by
      rw [Measure.pi_pi]
      simp only [localMultiplicativeHaar_integerUnits, Finset.prod_const_one]

/-- The actual full diagonal-torus integral inherits ambient integrability
for every measurable right-principal-fixed complex function. -/
theorem integrable_diagonalUnits_of_principalFixed (n a : ℕ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Measurable f)
    (hfixed : ∀ k ∈ principalLevelSubgroup F.Carrier n a, ∀ g, f (g * k) = f g)
    (hi : Integrable f (generalLinearHaar F.Carrier n)) :
    Integrable (fun x : Fin (n + 1) → F.Carrierˣ => f (Iwasawa.diagonalUnits x))
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
  have hKpos : generalLinearHaar F.Carrier n (principalLevelSubgroup F.Carrier n a : Set _) ≠ 0 :=
    ((principalLevelOpenSubgroup F.Carrier n a).isOpen.measure_pos _
      ⟨1, one_mem _⟩).ne'
  have hpre := (measure_diagonalUnits_preimage_principalLevel_le_one F n a).trans_lt
    ENNReal.one_lt_top
  have : SigmaFinite (localMultiplicativeHaar F.Carrier) := inferInstance
  have : SigmaFinite (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) :=
    inferInstance
  exact integrable_subgroup_of_right_invariant (generalLinearHaar F.Carrier n)
    (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
    Iwasawa.diagonalUnits (continuous_diagonalUnits (n + 1)).measurable
    (principalLevelSubgroup F.Carrier n a)
    (principalLevelOpenSubgroup F.Carrier n a).isOpen.measurableSet hKpos hpre.ne f hf hfixed hi

/-- The literal full-matrix integrand restricted to the full diagonal torus. -/
def matrixDiagonalIntegrand {n : ℕ} (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (a : Fin (n + 1) → F.Carrierˣ) : ℂ :=
  matrixIntegrand abv Φ s f (Iwasawa.diagonalUnits a)

/-- A genuinely convergent bi-smooth matrix integrand is integrable on the
full diagonal torus for its actual product multiplicative Haar measure. -/
theorem integrable_biSmooth_matrixDiagonalIntegrand
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients σ) (s : ℂ)
    (hi : GodementJacquet.Padic.MatrixConverges F Φ s f.val) :
    Integrable (matrixDiagonalIntegrand F Φ s f.val)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
  obtain ⟨a, ha, hfixed⟩ := matrixIntegrand_exists_principalFixed F σ Φ f
  exact integrable_diagonalUnits_of_principalFixed F n a _
    (measurable_biSmooth_matrixIntegrand F σ Φ f s) (hfixed s) hi

/-- The same common shifted matrix half-plane works for all the actual
full diagonal restrictions, without any uniformizer choice. -/
theorem biSmooth_matrixDiagonal_convergesOnRight
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F σ) :
    ∃ b : ℝ, ∀ Φ : MatrixTestFunction n F.Carrier, ∀ f : biSmoothMatrixCoefficients σ,
      ∀ s : ℂ, b < s.re →
      Integrable (matrixDiagonalIntegrand F Φ (s + jpssShift n) f.val)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
  obtain ⟨b, hb⟩ := hMatrix
  exact ⟨b, fun Φ f s hs =>
    integrable_biSmooth_matrixDiagonalIntegrand F σ Φ f (s + jpssShift n) (hb Φ f s hs)⟩

end Langlands.RankinSelberg
