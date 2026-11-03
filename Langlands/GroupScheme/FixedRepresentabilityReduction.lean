import Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement
import Langlands.GroupScheme.FixedActionEqualizer
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.FixedRepresentabilityFieldReduction

/-! # Conditional reduction to the generic closed-factorization locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The generic closed-factorization locus supplies the fixed-subgroup
representative through the action equalizer. -/
theorem fixedSubgroupRepresentability_of_closedFactorizationLocus
    (h : Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement.{u}) :
    FixedSubgroupRepresentabilityStatement.{u} := by
  intro R H G hH hflat hprojective hG a
  let := hG
  obtain ⟨Z, i, hi, hpoints⟩ := h R H.X hH hflat hprojective
    G.X a.actionEqualizer a.actionEqualizerInclusion inferInstance
  let := hi
  have : Mono i := Over.mono_of_mono_left i
  apply a.fixedSubgroup.isClosedRepresentable_of_scheme i
  intro T g
  exact (a.mem_fixedSubgroup_iff_factors_actionEqualizer g).trans (hpoints T g).symm

/-- The field fixed-subgroup target follows from the same geometric input. -/
theorem fieldFixedSubgroupRepresentability_of_closedFactorizationLocus
    (h : Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement.{u}) :
    FieldFixedSubgroupRepresentabilityStatement.{u} :=
  fieldFixedSubgroupRepresentability_of_general
    (fixedSubgroupRepresentability_of_closedFactorizationLocus h)

/-- The all-test field centralizer target follows from the same geometric input. -/
theorem fieldCentralizerRepresentability_of_closedFactorizationLocus
    (h : Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement.{u}) :
    FieldCentralizerRepresentabilityStatement.{u} :=
  fieldCentralizerRepresentability_of_fixed
    (fieldFixedSubgroupRepresentability_of_closedFactorizationLocus h)

end Langlands.GroupScheme
