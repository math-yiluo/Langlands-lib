import Langlands.Representation.Compact.CompactGroupIsotypicDecompositionStatement
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily

/-! # The isotypic decomposition of a smooth compact-group representation -/

noncomputable section

universe u v

namespace Langlands.Renard.CompactRepresentation

open CompactCoefficientClass MeasureTheory TopologicalSpace

/-- Renard IV.1.1, Corollary, with the published intrinsic isotypic components. -/
theorem compactGroupIsotypicDecomposition :
    CompactGroupIsotypicDecompositionStatement.{u, v} := by
  intro K _ _ _ _ _ _ π
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure (⊤ : PositiveCompacts K)
  have hcof : ∀ L : OpenSubgroup K,
      ∃ M : OpenSubgroup K, IsCompact (M : Set K) ∧ M ≤ L := by
    intro L
    exact ⟨L, L.isClosed.isCompact, le_rfl⟩
  have hcompact : HasCompactSmoothDualCoefficients π.representation := by
    intro x ℓ hℓ
    exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
  refine ⟨?_, totalIsotypicSubrepresentation_eq_top_of_compactCoefficients μ π hcompact⟩
  rw [iSupIndep_def]
  intro c
  have hcompl := CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
    μ hcof c π
  have hle : (⨆ (d : CompactCoefficientClass.{u, v} K) (_ : d ≠ c),
      isotypicSubrepresentation d π) ≤ annihilatorSubrepresentation c π :=
    iSup₂_le fun d hd => isotypicSubrepresentation_le_annihilator_of_ne hd π
  apply disjoint_iff.mpr
  apply _root_.Subrepresentation.toSubmodule_injective
  have hle' : (⨆ (d : CompactCoefficientClass.{u, v} K) (_ : d ≠ c),
      isotypicSubrepresentation d π).toSubmodule ≤
      (annihilatorSubrepresentation c π).toSubmodule := hle
  exact (hcompl.disjoint.mono_right hle').eq_bot

end Langlands.Renard.CompactRepresentation
