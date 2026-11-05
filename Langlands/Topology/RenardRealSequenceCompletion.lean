import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Real product sequences and their finite-support subspace

Concrete internal constructions motivated by Renard, Appendix A.III.1,
example 2 (2026 edition, printed p.252 / PDF258). See the paired Markdown
for provenance and the distinction between the constructed maps and later
completion or continuous-extension assertions.
-/

noncomputable section

namespace Langlands.Renard.RealSequenceCompletion

/-- Real sequences with the usual pointwise operations and product structures. -/
abbrev ProductSequence : Type := ℕ → ℝ

/-- The range of the actual linear inclusion of finitely supported functions. -/
def finiteSequenceSubmodule : Submodule ℝ ProductSequence :=
  LinearMap.range (Finsupp.lcoeFun (R := ℝ) : (ℕ →₀ ℝ) →ₗ[ℝ] ProductSequence)

/-- The finite-support subspace, with inherited subtype topology and uniformity. -/
abbrev FiniteSequence : Type := ↥finiteSequenceSubmodule

@[simp]
theorem mem_finiteSequenceSubmodule (p : ProductSequence) :
    p ∈ finiteSequenceSubmodule ↔ (Function.support p).Finite := by
  constructor
  · rintro ⟨f, rfl⟩
    exact f.hasFiniteSupport
  · intro hp
    exact ⟨Finsupp.ofSupportFinite p hp, rfl⟩

/-- The inherited subtype topology is the topology induced by inclusion. -/
theorem finiteSequence_topologicalSpace :
    (inferInstance : TopologicalSpace FiniteSequence) =
      TopologicalSpace.induced (Subtype.val : FiniteSequence → ProductSequence)
        (inferInstance : TopologicalSpace ProductSequence) := rfl

/-- The inherited subtype uniformity is the uniformity induced by inclusion. -/
theorem finiteSequence_uniformSpace :
    (inferInstance : UniformSpace FiniteSequence) =
      UniformSpace.comap (Subtype.val : FiniteSequence → ProductSequence)
        (inferInstance : UniformSpace ProductSequence) := rfl

theorem productSequence_isTopologicalAddGroup : IsTopologicalAddGroup ProductSequence :=
  inferInstance

theorem finiteSequence_isTopologicalAddGroup : IsTopologicalAddGroup FiniteSequence :=
  inferInstance

theorem productSequence_continuousSMul : ContinuousSMul ℝ ProductSequence :=
  inferInstance

theorem finiteSequence_continuousSMul : ContinuousSMul ℝ FiniteSequence :=
  inferInstance

theorem productSequence_isUniformAddGroup : IsUniformAddGroup ProductSequence :=
  inferInstance

/-- The additive uniform structure pulled back along the actual linear inclusion. -/
instance finiteSequence_isUniformAddGroup : IsUniformAddGroup FiniteSequence :=
  IsUniformAddGroup.comap finiteSequenceSubmodule.subtype

/-- Fixed-scalar uniform continuity for the product additive uniformity. -/
instance productSequence_uniformContinuousConstSMul :
    UniformContinuousConstSMul ℝ ProductSequence :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ ProductSequence

/-- Fixed-scalar uniform continuity for the inherited subspace uniformity. -/
instance finiteSequence_uniformContinuousConstSMul :
    UniformContinuousConstSMul ℝ FiniteSequence :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ FiniteSequence

theorem productSequence_completeSpace : CompleteSpace ProductSequence := inferInstance

theorem productSequence_t2Space : T2Space ProductSequence := inferInstance

/-- The continuous real-linear inclusion of the inherited subspace. -/
def inclusion : FiniteSequence →L[ℝ] ProductSequence :=
  finiteSequenceSubmodule.subtypeL

@[simp]
theorem inclusion_apply (x : FiniteSequence) : inclusion x = x.val := rfl

@[simp]
theorem inclusion_apply_coord (x : FiniteSequence) (i : ℕ) :
    inclusion x i = x.val i := rfl

theorem inclusion_injective : Function.Injective inclusion := Subtype.val_injective

theorem inclusion_isUniformEmbedding : IsUniformEmbedding inclusion :=
  isUniformEmbedding_subtype_val

/-- The constant-one sequence, for the later fixed-real extension investigation. -/
def missingSequence : ProductSequence := fun _ => 1

@[simp]
theorem missingSequence_apply (i : ℕ) : missingSequence i = 1 := rfl

/-- An actual finitely supported function with support inside `Finset.range n`. -/
def truncateFinsupp (n : ℕ) (p : ProductSequence) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.range n) (fun i => if i < n then p i else 0) (by
    intro i hi
    by_cases h : i < n
    · exact Finset.mem_range.mpr h
    · simp [h] at hi)

@[simp]
theorem truncateFinsupp_apply (n : ℕ) (p : ProductSequence) (i : ℕ) :
    truncateFinsupp n p i = if i < n then p i else 0 := rfl

theorem truncateFinsupp_support_subset (n : ℕ) (p : ProductSequence) :
    (truncateFinsupp n p).support ⊆ Finset.range n :=
  Finsupp.support_onFinset_subset

/-- The finite truncation, with its explicit witness in the range of `lcoeFun`. -/
def truncate (n : ℕ) (p : ProductSequence) : FiniteSequence :=
  ⟨Finsupp.lcoeFun (R := ℝ) (truncateFinsupp n p), ⟨truncateFinsupp n p, rfl⟩⟩

@[simp]
theorem inclusion_truncate (n : ℕ) (p : ProductSequence) (i : ℕ) :
    inclusion (truncate n p) i = if i < n then p i else 0 := rfl

@[simp]
theorem truncate_zero (p : ProductSequence) : truncate 0 p = 0 := by
  apply Subtype.ext
  funext i
  change (if i < 0 then p i else 0) = 0
  simp

/-- The explicit compatible countable-product metric; never a global instance. -/
@[instance_reducible]
def sequenceMetricSpace : MetricSpace ProductSequence := PiCountable.metricSpace

/-- This metric retains the original product uniformity. -/
theorem sequenceMetricSpace_uniformSpace :
    sequenceMetricSpace.toUniformSpace = (inferInstance : UniformSpace ProductSequence) := rfl

/-- Its topology is consequently the original product topology. -/
theorem sequenceMetricSpace_topologicalSpace :
    sequenceMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ProductSequence) := rfl

/-- Distance computed with the explicit countable-product metric. -/
def sequenceDistance (p q : ProductSequence) : ℝ :=
  @dist ProductSequence sequenceMetricSpace.toDist p q

theorem sequenceDistance_eq_tsum (p q : ProductSequence) :
    sequenceDistance p q =
      ∑' i, min ((2⁻¹ : ℝ) ^ Encodable.encode i) (dist (p i) (q i)) := rfl

/-- The raw reciprocal-distance function, using the total inverse on `ℝ`. -/
def reciprocalDistance (x : FiniteSequence) : ℝ :=
  (sequenceDistance (inclusion x) missingSequence)⁻¹

@[simp]
theorem reciprocalDistance_apply (x : FiniteSequence) :
    reciprocalDistance x = (sequenceDistance (inclusion x) missingSequence)⁻¹ := rfl

/-- The actual uniform completion of the inherited finite-support uniformity. -/
abbrev SequenceCompletion : Type := UniformSpace.Completion FiniteSequence

/-- The canonical map to that actual completion as a continuous real-linear map. -/
def toCompletion : FiniteSequence →L[ℝ] SequenceCompletion :=
  UniformSpace.Completion.toComplL

theorem coe_toCompletion :
    (toCompletion : FiniteSequence → SequenceCompletion) =
      ((↑) : FiniteSequence → UniformSpace.Completion FiniteSequence) := rfl

@[simp]
theorem toCompletion_apply (x : FiniteSequence) :
    toCompletion x = (x : UniformSpace.Completion FiniteSequence) := rfl

/-- Extend the actual inclusion into the complete separated product. -/
def completionToProduct : SequenceCompletion →L[ℝ] ProductSequence :=
  ContinuousLinearMap.fromCompletion inclusion

theorem coe_completionToProduct :
    (completionToProduct : SequenceCompletion → ProductSequence) =
      UniformSpace.Completion.extension inclusion := rfl

@[simp]
theorem completionToProduct_coe (x : FiniteSequence) :
    completionToProduct (x : UniformSpace.Completion FiniteSequence) = inclusion x :=
  ContinuousLinearMap.fromCompletion_apply_coe inclusion x

@[simp]
theorem completionToProduct_toCompletion (x : FiniteSequence) :
    completionToProduct (toCompletion x) = inclusion x :=
  completionToProduct_coe x

end Langlands.Renard.RealSequenceCompletion
