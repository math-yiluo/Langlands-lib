import Langlands.LocalFactor.Abelian.ZetaAnalysisHelpers
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

/-- The annulus of nonzero elements with specified additive order. -/
def orderShell (k : ℤ) : Set F.Carrier := {x | x ≠ 0 ∧ T.ord x = k}

/-- The order and Gauss indexing conventions differ by a sign. -/
theorem orderShell_eq_gaussShell (k : ℤ) :
    orderShell T k = gaussShell T (-k) := by simp [orderShell, gaussShell]

/-- Every order shell is compact and Borel measurable. -/
theorem orderShell_compact_measurable (k : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    IsCompact (orderShell T k) ∧ MeasurableSet (orderShell T k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  rw [orderShell_eq_gaussShell, gaussShell_eq_valuationShell]
  exact ⟨(T.valuationShell_compact_closed _).1,
    (T.valuationShell_compact_closed _).2.measurableSet⟩

/-- The integral units are the zeroth shell. -/
theorem integralUnits_eq_orderShell_zero : integralUnits T = orderShell T 0 := rfl

/-- Multiplication by a power of any uniformizer identifies the unit annulus with each shell. -/
theorem mul_uniformizer_mem_orderShell_iff (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (k : ℤ) (x : F.Carrier) :
    ((π ^ k : F.Carrierˣ) : F.Carrier) * x ∈ orderShell T k ↔
      x ∈ integralUnits T := by
  by_cases hx : x = 0
  · subst x
    simp [orderShell, integralUnits]
  · have hord : T.ord (((π ^ k : F.Carrierˣ) : F.Carrier) * x) = k + T.ord x := by
      rw [T.ord_mul (π ^ k).ne_zero hx, Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one]
    simp only [orderShell, integralUnits, Set.mem_ofPred_eq, mul_ne_zero_iff, ne_eq,
      (π ^ k).ne_zero, hx, not_false_eq_true, true_and, hord, add_eq_left]

/-- The scalar pushforward formula as an actual Bochner change of variables. -/
theorem integral_comp_mul_scalar (μ : LocalHaar)
    (a : F.Carrierˣ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : F.Carrier → E) :
    letI := T.topology
    letI := borel F.Carrier
    (∫ x, g ((a : F.Carrier) * x) ∂μ.measure) =
      (T.normalizedAbs (a : F.Carrier))⁻¹ • ∫ x, g x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have he : MeasurableEmbedding (fun x : F.Carrier => (a : F.Carrier) * x) :=
    (MeasurableEquiv.mulLeft₀ (a : F.Carrier) a.ne_zero).measurableEmbedding
  rw [← he.integral_map g, HarmonicAnalysis.padicScalarHaarScaling F T μ.measure a,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv, T.normalizedAbsUnits_coe]

/-- Actual integration over an annulus, for any integrand, reduces to the unit annulus. -/
theorem setIntegral_orderShell (μ : LocalHaar)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (k : ℤ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : F.Carrier → E) :
    letI := T.topology
    letI := borel F.Carrier
    (∫ x in orderShell T k, g x ∂μ.measure) =
      (T.residueCardinality : ℝ) ^ (-k) •
        ∫ x in integralUnits T, g (((π ^ k : F.Carrierˣ) : F.Carrier) * x) ∂μ.measure := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hU : MeasurableSet (integralUnits T) := (orderShell_compact_measurable T 0).2
  have hS := (orderShell_compact_measurable T k).2
  have ha : T.normalizedAbs ((π ^ k : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-k) := by
    rw [T.normalizedAbs_of_ne_zero (π ^ k).ne_zero,
      Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one]
  have hcomp : (fun x => (orderShell T k).indicator g
      (((π ^ k : F.Carrierˣ) : F.Carrier) * x)) =
      (integralUnits T).indicator
        (fun x => g (((π ^ k : F.Carrierˣ) : F.Carrier) * x)) := by
    funext x
    simp only [Set.indicator_apply, mul_uniformizer_mem_orderShell_iff T π hπ]
  have h := integral_comp_mul_scalar T μ (π ^ k) ((orderShell T k).indicator g)
  rw [hcomp, integral_indicator hU, integral_indicator hS, ha] at h
  have hq : (T.residueCardinality : ℝ) ^ (-k) ≠ 0 :=
    (zpow_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)) _).ne'
  rw [h, smul_smul, mul_inv_cancel₀ hq, one_smul]

/-- The order shells are disjoint. -/
theorem pairwise_disjoint_orderShell : Pairwise (fun k l : ℤ =>
    Disjoint (orderShell T k) (orderShell T l)) := by
  intro k l hkl
  exact Set.disjoint_left.mpr fun x hx hy => hkl (hx.2.symm.trans hy.2)

/-- The order shells cover every nonzero element. -/
theorem iUnion_orderShell : (⋃ k : ℤ, orderShell T k) = {0}ᶜ := by
  ext x
  simp only [Set.mem_iUnion, orderShell, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨T.ord x, h, rfl⟩⟩

end Langlands.LocalFactor.PadicAbelian
