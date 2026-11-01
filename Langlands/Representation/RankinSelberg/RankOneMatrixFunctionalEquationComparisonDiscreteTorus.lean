import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonHaarRestriction
import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof
import Langlands.Representation.Conductor.PrincipalCongruence
import Langlands.Group.GL.UpperBruhatCells
import Langlands.Group.GL.CountabilityProof
import Mathlib.Algebra.Group.TypeTags.Finite

/-! Actual uniformizer-torus summability from ambient matrix convergence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Topology Conductor
open scoped ENNReal NNReal

universe uF

/-- Uniformizer powers in each diagonal entry, with the additive exponent
lattice viewed as a multiplicative group. -/
def uniformizerTorusHom {K : Type*} [Field K] (n : ℕ) (ϖ : Kˣ) :
    Multiplicative (Fin (n + 1) → ℤ) →* Langlands.GeneralLinear (n + 1) K where
  toFun e := Iwasawa.torus ϖ e.toAdd
  map_one' := by
    change Iwasawa.diagonalUnits (fun _ : Fin (n + 1) => ϖ ^ (0 : ℤ)) = 1
    simp only [zpow_zero]
    exact map_one _
  map_mul' e f := by
    change Iwasawa.diagonalUnits (fun i => ϖ ^ (e.toAdd i + f.toAdd i)) =
      Iwasawa.diagonalUnits (fun i => ϖ ^ e.toAdd i) *
        Iwasawa.diagonalUnits (fun i => ϖ ^ f.toAdd i)
    rw [← map_mul]
    congr 1
    funext i
    exact zpow_add ϖ _ _

@[simp] theorem uniformizerTorusHom_apply {K : Type*} [Field K]
    (n : ℕ) (ϖ : Kˣ) (e : Multiplicative (Fin (n + 1) → ℤ)) :
    uniformizerTorusHom n ϖ e = Iwasawa.torus ϖ e.toAdd := rfl

local instance torusExponentCountable (n : ℕ) :
    Countable (Multiplicative (Fin (n + 1) → ℤ)) :=
  Countable.of_equiv (Fin (n + 1) → ℤ) Multiplicative.ofAdd

local instance torusExponentMeasurable (n : ℕ) :
    MeasurableSpace (Multiplicative (Fin (n + 1) → ℤ)) := ⊤

local instance torusExponentSingleton (n : ℕ) :
    MeasurableSingletonClass (Multiplicative (Fin (n + 1) → ℤ)) := ⟨fun _ => trivial⟩

/-- The pure uniformizer torus meets every actual principal level only at
its identity exponent. -/
theorem uniformizerTorusHom_preimage_principalLevel
    {K : Type*} [Field K] [ValuativeRel K] (n a : ℕ) (ϖ : Kˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ) :
    uniformizerTorusHom n ϖ ⁻¹' (principalLevelSubgroup K n a : Set _) = {1} := by
  ext e
  constructor
  · intro he
    have hInt := principalLevelSubgroup_antitone K n (Nat.zero_le a) he
    rw [principalLevelSubgroup_zero] at hInt
    have hentries := (mem_integralSubgroup (ValuativeRel.valuation K).integer n _).1 hInt
    have hpow (i : Fin (n + 1)) :
        ϖ ^ e.toAdd i ∈ integralUnits (ValuativeRel.valuation K).integer := by
      apply (mem_integralUnits _ _).2
      constructor
      · simpa only [uniformizerTorusHom_apply, Iwasawa.torus, Iwasawa.diagonalUnits_val,
          Matrix.diagonal_apply_eq] using hentries.1 i i
      · simpa only [uniformizerTorusHom_apply, Iwasawa.torus, ← map_inv,
          Iwasawa.diagonalUnits_val, Pi.inv_apply, Matrix.diagonal_apply_eq] using hentries.2 i i
    have he0 (i : Fin (n + 1)) : e.toAdd i = 0 :=
      zpow_eq_of_mul_integralUnits hϖ (one_mem _) (hpow i) (by simp)
    apply Set.mem_singleton_iff.mpr
    change Multiplicative.ofAdd e.toAdd = Multiplicative.ofAdd (0 : Fin (n + 1) → ℤ)
    congr 1
    funext i
    exact he0 i
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst e
    simp only [map_one, Set.mem_preimage, SetLike.mem_coe]
    exact one_mem _

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance discreteTorusTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance discreteTorusValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance discreteTorusLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance discreteTorusT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance discreteTorusSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance discreteTorusMeasurable : MeasurableSpace F.Carrier := borel _
local instance discreteTorusBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance discreteTorusGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance discreteTorusGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance discreteTorusGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance discreteTorusGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

/-- The actual counting Haar integral of the uniformizer-torus restriction
inherits ambient integrability for a principal-fixed function. -/
theorem integrable_uniformizerTorus_of_principalFixed
    (n a : ℕ) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Measurable f)
    (hfixed : ∀ k ∈ principalLevelSubgroup F.Carrier n a, ∀ g, f (g * k) = f g)
    (hi : Integrable f (generalLinearHaar F.Carrier n)) :
    Integrable (fun e : Multiplicative (Fin (n + 1) → ℤ) => f (Iwasawa.torus ϖ e.toAdd))
      Measure.count := by
  have hKpos : generalLinearHaar F.Carrier n (principalLevelSubgroup F.Carrier n a : Set _) ≠ 0 :=
    ((principalLevelOpenSubgroup F.Carrier n a).isOpen.measure_pos _
      ⟨1, one_mem _⟩).ne'
  have hpre : (Measure.count : Measure (Multiplicative (Fin (n + 1) → ℤ)))
      (uniformizerTorusHom n ϖ ⁻¹' (principalLevelSubgroup F.Carrier n a : Set _)) ≠ ⊤ := by
    rw [uniformizerTorusHom_preimage_principalLevel n a ϖ hϖ]
    simp
  exact integrable_subgroup_of_right_invariant (generalLinearHaar F.Carrier n) Measure.count
    (uniformizerTorusHom n ϖ) (measurable_of_countable _) (principalLevelSubgroup F.Carrier n a)
    (principalLevelOpenSubgroup F.Carrier n a).isOpen.measurableSet hKpos hpre f hf hfixed hi

/-- The corresponding genuine discrete norm sum is finite. -/
theorem tsum_enorm_uniformizerTorus_lt_top_of_principalFixed
    (n a : ℕ) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Measurable f)
    (hfixed : ∀ k ∈ principalLevelSubgroup F.Carrier n a, ∀ g, f (g * k) = f g)
    (hi : Integrable f (generalLinearHaar F.Carrier n)) :
    (∑' e : Multiplicative (Fin (n + 1) → ℤ), ‖f (Iwasawa.torus ϖ e.toAdd)‖ₑ) < ⊤ := by
  have h := integrable_uniformizerTorus_of_principalFixed F n a ϖ hϖ f hf hfixed hi
  simpa only [lintegral_count] using (hasFiniteIntegral_iff_enorm.mp h.hasFiniteIntegral)

end Langlands.RankinSelberg
