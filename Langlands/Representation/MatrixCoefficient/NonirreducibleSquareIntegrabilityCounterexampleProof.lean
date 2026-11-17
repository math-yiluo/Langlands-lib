import Langlands.Representation.MatrixCoefficient.NonirreducibleSquareIntegrabilityCounterexampleStatement
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.AlexandrovDiscrete

/-! # A nonirreducible representation with one square-integrable coefficient -/

noncomputable section

open MeasureTheory
open scoped MonoidAlgebra ENNReal

namespace Langlands.Renard.CompactRepresentation

namespace NonirreducibleCounterexample

private abbrev D := DihedralGroup 0

local instance : TopologicalSpace D := ⊥
local instance : DiscreteTopology D := ⟨rfl⟩
local instance : MeasurableSpace D := borel D
local instance : BorelSpace D := ⟨rfl⟩

private abbrev Q := D ⧸ Subgroup.center D

local instance : DiscreteTopology Q :=
  QuotientGroup.discreteTopology_iff.mpr (isOpen_discrete _)

local instance : MeasurableSpace Q := borel Q
local instance : BorelSpace Q := ⟨rfl⟩

private theorem count_haar (H : Type*) [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H] :
    (Measure.count : Measure H).IsHaarMeasure where
  lt_top_of_isCompact _ h := Measure.count_apply_lt_top.mpr h.finite_of_discrete
  open_pos _ _ h := Measure.count_ne_zero h

local instance : (Measure.count : Measure D).IsHaarMeasure := count_haar D
local instance : (Measure.count : Measure Q).IsHaarMeasure := count_haar Q

private theorem mk_injective : Function.Injective (QuotientGroup.mk : D → Q) := by
  intro g h e
  have hmem := QuotientGroup.eq.mp e
  rw [DihedralGroup.center_eq_bot_of_zero, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

local instance : Infinite Q := Infinite.of_injective _ mk_injective

private abbrev V := ℂ[D]
private abbrev ρ : Representation ℂ D V := Representation.leftRegular ℂ D

private theorem discrete_smooth {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ D W) : IsSmooth σ := by
  intro v
  refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
  change ∀ g : (⊥ : Subgroup D), σ (g : D) v = v
  intro g
  have hg : (g : D) = 1 := g.property
  simp [hg]

private abbrev π : SmoothRep ℂ D := SmoothRep.of ρ (discrete_smooth ρ)

private def evaluation : Module.Dual ℂ V :=
  (Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private def augmentation : Module.Dual ℂ V :=
  (Finsupp.linearCombination ℂ (fun _ : D => (1 : ℂ))).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private def smoothFunctional (f : Module.Dual ℂ V) : SmoothDual ρ :=
  ⟨f, discrete_smooth ρ.dual f⟩

private abbrev δ : V := MonoidAlgebra.single 1 1

@[simp] private theorem evaluation_single (g : D) (a : ℂ) :
    evaluation (MonoidAlgebra.single g a) = if g = 1 then a else 0 := by
  simp [evaluation, Finsupp.single_apply]

@[simp] private theorem augmentation_single (g : D) (a : ℂ) :
    augmentation (MonoidAlgebra.single g a) = a := by
  simp [augmentation]

private theorem augmentation_action (g : D) (v : V) : augmentation (ρ g v) = augmentation v := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw]
  | single h a => simp [ρ, Representation.ofMulAction_single]

private def augmentationKernel : Subrepresentation ρ where
  toSubmodule := augmentation.ker
  apply_mem_toSubmodule g v hv := by
    change augmentation (ρ g v) = 0
    rw [augmentation_action]
    exact hv

private theorem not_irreducible : ¬ π.IsIrreducible := by
  intro h
  let : Representation.IsIrreducible ρ := h
  rcases eq_bot_or_eq_top augmentationKernel with hb | ht
  · have hm : MonoidAlgebra.single (DihedralGroup.sr 0) (1 : ℂ) - δ ∈
        augmentationKernel := by
      change augmentation _ = 0
      simp
    rw [hb] at hm
    have he : MonoidAlgebra.single (DihedralGroup.sr 0) (1 : ℂ) - δ = 0 := hm
    have := congrArg evaluation he
    have hs : (DihedralGroup.sr 0 : D) ≠ 1 := by intro e; cases e
    simp [δ, hs] at this
  · have hm : δ ∈ augmentationKernel := by rw [ht]; trivial
    change augmentation δ = 0 at hm
    simp [δ] at hm

private def centralCharacter : UnitaryCentralCharacter ρ where
  character := 1
  isOpen_ker := isOpen_discrete _
  norm_eq_one _ := by simp
  acts z v := by
    have hz : (z : D) = 1 := by
      have := z.property
      simpa [DihedralGroup.center_eq_bot_of_zero] using this
    simp [hz]

private theorem good_coefficient (g : D) :
    matrixCoefficient ρ (smoothFunctional evaluation) δ g = if g = 1 then 1 else 0 := by
  simp [matrixCoefficient, smoothFunctional, δ, ρ, Representation.ofMulAction_single]

private theorem bad_coefficient (g : D) :
    matrixCoefficient ρ (smoothFunctional augmentation) δ g = 1 := by
  simp [matrixCoefficient, smoothFunctional, δ, ρ, Representation.ofMulAction_single]

private theorem good_norm :
    centralCharacter.coefficientNorm (smoothFunctional evaluation) δ =
      Set.indicator ({1} : Set Q) (fun _ => (1 : ℝ)) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [UnitaryCentralCharacter.coefficientNorm_mk, good_coefficient]
    have hq : (QuotientGroup.mk g : Q) = 1 ↔ g = 1 := by
      exact mk_injective.eq_iff
    by_cases hg : g = 1 <;> simp [hg, hq]

private theorem good_memLp :
    MemLp (centralCharacter.coefficientNorm (smoothFunctional evaluation) δ) 2
      (Measure.count : Measure Q) := by
  rw [good_norm]
  exact memLp_indicator_const 2 (measurableSet_singleton 1) 1
    (Or.inr (by simp))

private theorem bad_norm :
    centralCharacter.coefficientNorm (smoothFunctional augmentation) δ =
      fun _ : Q => (1 : ℝ) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => simp [UnitaryCentralCharacter.coefficientNorm_mk, bad_coefficient]

private theorem not_squareIntegrable : ¬ π.IsSquareIntegrableModuloCenter
    (Measure.count : Measure Q) := by
  rintro ⟨c, hc⟩
  have hm := hc (smoothFunctional augmentation) δ
  rw [c.coefficientNorm_eq centralCharacter, bad_norm] at hm
  have hfin := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hm
  simp [Measure.count_apply_infinite Set.infinite_univ] at hfin

private theorem counterexample : NonirreducibleSquareIntegrabilityCounterexampleStatement := by
  intro h
  apply not_squareIntegrable
  apply h D (Measure.count : Measure D) (Measure.count : Measure Q) π not_irreducible
    centralCharacter
  refine ⟨smoothFunctional evaluation, δ, ?_, good_memLp⟩
  intro hz
  have he := congrFun hz (1 : D)
  change matrixCoefficient ρ (smoothFunctional evaluation) δ (1 : D) = 0 at he
  simp [good_coefficient] at he

end NonirreducibleCounterexample

/-- Renard IV.3.2, Remark: without irreducibility, one nonzero square-integrable
coefficient does not imply square-integrability of every smooth coefficient. -/
theorem nonirreducibleSquareIntegrabilityCounterexample :
    NonirreducibleSquareIntegrabilityCounterexampleStatement :=
  NonirreducibleCounterexample.counterexample

end Langlands.Renard.CompactRepresentation
