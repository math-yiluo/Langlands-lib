import Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlices
import Langlands.AllField.Representation.RankinSelberg.ValuationShellIntegrationStatement
/-!
# Proof of the valuation-shell decomposition of multiplicative Haar integrals

The specified uniformizer has order one. The order is a continuous homomorphism
from the units to the discrete integers, so the shells of fixed order are open,
disjoint and cover the units, and each is the translate of the order-zero
shell, which is the group of integral units. Left invariance of the normalized
Haar measure turns every shell integral into an integral over the integral
units, and the countable disjoint-union integral lemmas give the integrability
criterion and the integral identity.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ValuationShellIntegrationStatement continuous_ord_units normalizedAbsoluteValue normalizedAbsoluteValue_apply valuationShellIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory

universe uF

section Translation

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
  [μ.IsMulLeftInvariant] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Translation

/-- The units of a nonarchimedean local field, with supplied data `T`, are the disjoint
union of the valuation shells, each a uniformizer translate of the integral units of
normalized Haar mass one, and the actual multiplicative Haar integral of a continuous
function is the sum of its shell integrals. -/
theorem valuationShellIntegration : ValuationShellIntegrationStatement.{uF} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace Fˣ := borel Fˣ
  have : BorelSpace Fˣ := ⟨rfl⟩
  intro μ K S
  have hq1 : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  -- The order map on units and the uniformizer.
  let ord : Fˣ → ℤ := fun a => T.ord (a : F)
  have hordc : Continuous ord := continuous_ord_units T
  let π : Fˣ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T
  have hπ : T.ord (π : F) = 1 := Langlands.LocalFactor.LocalAbelian.uniformizerUnit_ord T
  have hord (n : ℤ) (a : Fˣ) : ord (π ^ n * a) = n + ord a := by
    change T.ord ((π ^ n * a : Fˣ) : F) = _
    rw [Units.val_mul, T.ord_mul (π ^ n).ne_zero a.ne_zero, Units.val_zpow_eq_zpow_val,
      T.ord_zpow, hπ, mul_one]
  -- The order-zero shell is the group of integral units.
  have hS0 : S 0 = K := by
    ext a
    change T.ord (a : F) = 0 ↔ a ∈ integralUnits T.Integers
    rw [mem_integralUnits, ← T.normalizedAbs_le_one_iff_mem_integers,
      ← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_of_ne_zero a.ne_zero,
      T.normalizedAbs_of_ne_zero (a⁻¹).ne_zero, Units.val_inv_eq_inv_val, T.ord_inv,
      zpow_le_one_iff_right₀ hq1, zpow_le_one_iff_right₀ hq1]
    omega
  have hmemK (n : ℤ) (u : Fˣ) : u ∈ K ↔ π ^ n * u ∈ S n := by
    rw [← hS0]
    change ord u = 0 ↔ ord (π ^ n * u) = n
    rw [hord]
    omega
  have hSeq (n : ℤ) : S n = (fun u : Fˣ => π ^ n * u) '' K := by
    ext a
    constructor
    · intro ha
      refine ⟨(π ^ n)⁻¹ * a, (hmemK n _).2 ?_, mul_inv_cancel_left _ _⟩
      rwa [mul_inv_cancel_left]
    · rintro ⟨u, hu, rfl⟩
      exact (hmemK n u).1 hu
  -- Geometry of the shells.
  have hKc : IsCompact K := by
    have := localField_t2 F
    exact integralUnits_isCompact _
  have hKm : MeasurableSet K :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  have hK1 : μ K = 1 := localMultiplicativeHaar_integerUnits F
  have hSo (n : ℤ) : IsOpen (S n) := (isOpen_discrete ({n} : Set ℤ)).preimage hordc
  have hSm (n : ℤ) : MeasurableSet (S n) := (hSo n).measurableSet
  have hSc (n : ℤ) : IsCompact (S n) := by
    rw [hSeq n]
    exact hKc.image (continuous_const.mul continuous_id)
  have hSμ (n : ℤ) : μ (S n) = 1 := by
    rw [hSeq n, Set.image_mul_left, measure_preimage_mul, hK1]
  have hSabs (n : ℤ) : ∀ a ∈ S n,
      T.normalizedAbs (a : F) = (T.residueCardinality : ℝ) ^ (-n) := by
    intro a ha
    rw [T.normalizedAbs_of_ne_zero a.ne_zero, show T.ord (a : F) = n from ha]
  have hdisj : Pairwise (fun m n : ℤ => Disjoint (S m) (S n)) := fun m n hmn =>
    Set.disjoint_left.mpr fun a ha hb => hmn ((show ord a = m from ha).symm.trans hb)
  have hU : (⋃ n : ℤ, S n) = Set.univ :=
    Set.eq_univ_of_forall fun a => Set.mem_iUnion.mpr ⟨ord a, rfl⟩
  -- Shell integrals as translated integrals over the integral units.
  have hshell {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Fˣ → E)
      (n : ℤ) : ∫ u in K, g (π ^ n * u) ∂μ = ∫ a in S n, g a ∂μ :=
    setIntegral_comp_mul_left_of_mem_iff μ g (π ^ n) hKm (hSm n) (hmemK n)
  have hlocal (f : Fˣ → ℂ) (hf : Continuous f) (n : ℤ) : IntegrableOn f (S n) μ :=
    hf.continuousOn.integrableOn_compact' (hSc n) (hSm n)
  refine ⟨π, hπ, hS0, hdisj, hU,
    fun n => ⟨hSeq n, hSo n, hSc n, hSm n, hSμ n, hSabs n⟩, fun f hf => ⟨fun n => ?_, ?_⟩,
    fun f hf hfi => ?_⟩
  · exact (hf.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact'
      hKc hKm
  · simp_rw [hshell (fun a => ‖f a‖)]
    constructor
    · intro hfi
      exact (hasSum_integral_iUnion hSm hdisj
        (by rw [hU]; exact hfi.norm.integrableOn)).summable
    · intro hsum
      have h := integrableOn_iUnion_of_summable_integral_norm (hlocal f hf) hsum
      rwa [hU, integrableOn_univ] at h
  · have h := hasSum_integral_iUnion hSm hdisj (by rw [hU]; exact hfi.integrableOn)
    rw [hU, Measure.restrict_univ] at h
    simp_rw [hshell f]
    exact ⟨h.summable, h.tsum_eq.symm⟩

end Langlands.AllField.RankinSelberg
