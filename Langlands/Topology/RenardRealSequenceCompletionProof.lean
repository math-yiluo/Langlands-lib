import Langlands.Topology.RenardRealSequenceCompletionStatements

/-!
# The real-sequence completion and continuous nonextension

An internal fixed-real test of the canonical uniform-completion arrow under
the all-continuous-maps convention. See the paired Markdown.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Langlands.Renard.RealSequenceCompletion

theorem truncationsConverge : TruncationsConverge := by
  intro p
  apply tendsto_pi_nhds.mpr
  intro i
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (i + 1)] with n hn
  rw [inclusion_truncate]
  simp [Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn]

theorem inclusionDenseRange : InclusionDenseRange := by
  intro p
  exact mem_closure_of_tendsto (truncationsConverge p)
    (Filter.Eventually.of_forall fun n => ⟨truncate n p, rfl⟩)

theorem missingSequenceOutsideSubmodule : MissingSequenceOutsideSubmodule := by
  intro h
  have hf : (Set.univ : Set ℕ).Finite := by
    simpa [Function.support, missingSequence] using
      (mem_finiteSequenceSubmodule missingSequence).mp h
  exact Set.infinite_univ hf

theorem missingSequenceOutsideInclusion : MissingSequenceOutsideInclusion := by
  rintro ⟨x, hx⟩
  exact missingSequenceOutsideSubmodule (hx ▸ x.property)

theorem finiteSequenceIncomplete : FiniteSequenceIncomplete := by
  intro h
  let _ := h
  have hc := inclusion_isUniformEmbedding.isClosedEmbedding.isClosed_range
  apply missingSequenceOutsideInclusion
  rw [← hc.closure_eq]
  exact inclusionDenseRange missingSequence

theorem distanceToMissingPositive : DistanceToMissingPositive := by
  intro x
  let _ := sequenceMetricSpace
  change 0 < dist (inclusion x) missingSequence
  apply dist_pos.mpr
  intro h
  exact missingSequenceOutsideInclusion ⟨x, h⟩

theorem sequenceDistance_continuous :
    Continuous (fun p : ProductSequence => sequenceDistance p missingSequence) := by
  let _ := sequenceMetricSpace
  exact continuous_id.dist continuous_const

theorem reciprocalDistanceContinuous : ReciprocalDistanceContinuous := by
  exact (sequenceDistance_continuous.comp inclusion.continuous).inv₀
    (fun x => ne_of_gt (distanceToMissingPositive x))

theorem completionProductComparison : CompletionProductComparison := by
  let pkg : AbstractCompletion FiniteSequence :=
    { space := ProductSequence
      coe := inclusion
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := inclusion_isUniformEmbedding.isUniformInducing
      dense := inclusionDenseRange }
  let u : SequenceCompletion ≃ᵤ ProductSequence :=
    AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg pkg
  let e : SequenceCompletion ≃L[ℝ] ProductSequence :=
    { toFun := completionToProduct
      invFun := u.symm
      left_inv := u.left_inv
      right_inv := u.right_inv
      map_add' := completionToProduct.map_add
      map_smul' := completionToProduct.map_smul
      continuous_toFun := completionToProduct.continuous
      continuous_invFun := u.symm.uniformContinuous.continuous }
  exact ⟨e, rfl, completionToProduct_toCompletion⟩

theorem completionJointScalarContinuity : CompletionJointScalarContinuity := by
  obtain ⟨e, _, _⟩ := completionProductComparison
  refine ⟨?_⟩
  have hc : Continuous (fun z : ℝ × SequenceCompletion => e.symm (z.1 • e z.2)) :=
    e.symm.continuous.comp (continuous_fst.smul (e.continuous.comp continuous_snd))
  simpa only [map_smul, e.symm_apply_apply] using hc

theorem noProductContinuousExtension : NoProductContinuousExtension := by
  rintro ⟨g, hg, hx⟩
  have heq : (fun p : ProductSequence => sequenceDistance p missingSequence * g p) =
      (fun _ => (1 : ℝ)) :=
    inclusionDenseRange.equalizer (sequenceDistance_continuous.mul hg) continuous_const (by
      funext x
      change sequenceDistance (inclusion x) missingSequence * g (inclusion x) = 1
      rw [hx x, reciprocalDistance_apply,
        mul_inv_cancel₀ (ne_of_gt (distanceToMissingPositive x))])
  have hzero := congr_fun heq missingSequence
  let _ := sequenceMetricSpace
  change dist missingSequence missingSequence * g missingSequence = 1 at hzero
  simp at hzero

theorem noCompletionContinuousExtension : NoCompletionContinuousExtension := by
  obtain ⟨e, _, htri⟩ := completionProductComparison
  rintro ⟨g, hg, hx⟩
  apply noProductContinuousExtension
  refine ⟨fun p => g (e.symm p), hg.comp e.symm.continuous, ?_⟩
  intro x
  change g (e.symm (inclusion x)) = reciprocalDistance x
  rw [← htri x, e.symm_apply_apply]
  exact hx x

theorem completionCounterexampleStatements : CompletionCounterexampleStatements :=
  ⟨truncationsConverge, inclusionDenseRange, missingSequenceOutsideSubmodule,
    missingSequenceOutsideInclusion, finiteSequenceIncomplete,
    distanceToMissingPositive, reciprocalDistanceContinuous,
    completionProductComparison, completionJointScalarContinuity,
    noProductContinuousExtension, noCompletionContinuousExtension⟩

end Langlands.Renard.RealSequenceCompletion
