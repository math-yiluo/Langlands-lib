import Langlands.Representation.CompactCoefficient.ProjectorStatement
import Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.Hecke.CommonInvarianceProof

/-!
# Natural compact-isotypic projectors: proof

The intrinsic isotypic and annihilator subrepresentations of every
compact-coefficient class are complementary in every smooth representation
(`CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation`).
The projector along this splitting is the required family; its properties come
from the published conditional projector algebra.
-/

namespace Langlands

open MeasureTheory

universe uG uV uW

/-- Bernstein--Zelevinsky (1976), §§2.42--2.44: the natural compact-isotypic
projectors with intrinsic range and kernel. -/
theorem compactCoefficientProjector
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
    [Measure.IsMulRightInvariant μ] :
    CompactCoefficientProjectorStatement.{uG, uV, uW} G μ := by
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  have h : ∀ (c : CompactCoefficientClass.{uG, uV} G) (A : SmoothRep.{0, uG, uW} ℂ G),
      IsCompl (CompactCoefficientClass.isotypicSubrepresentation c A).toSubmodule
        (CompactCoefficientClass.annihilatorSubrepresentation c A).toSubmodule :=
    CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof
  refine ⟨CompactCoefficientClass.isotypicProjectorFamilyOfIsCompl h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c A
    exact Representation.IntertwiningMap.ext
      (CompactCoefficientClass.isotypicProjectorOfIsCompl_idempotent c (h c A)).eq
  · intro c A
    exact ⟨CompactCoefficientClass.isotypicProjectorOfIsCompl_range c (h c A),
      CompactCoefficientClass.isotypicProjectorOfIsCompl_ker c (h c A)⟩
  · intro c A B f
    ext v
    exact CompactCoefficientClass.isotypicProjectorOfIsCompl_natural c (h c A) (h c B) f v
  · intro c d hcd A
    exact CompactCoefficientClass.isotypicProjectorFamilyOfIsCompl_orthogonal h
      (Ne.symm hcd) A
  · intro c A
    refine hasCompactSmoothDualCoefficients_subrepresentation_of_le hcof A _ ?_
    rw [CompactCoefficientClass.isotypicProjectorFamilyOfIsCompl,
      CompactCoefficientClass.isotypicProjectorOfIsCompl_range]
    intro v hv
    exact CompactCoefficientClass.totalIsotypicSubrepresentation_le_compactCoefficientVectors A
      (CompactCoefficientClass.isotypicSubrepresentation_le_totalIsotypicSubrepresentation A c hv)
  · intro c A K _ hc v hv
    exact CompactCoefficientClass.isotypicProjectorFamilyOfIsCompl_vanishes_on_fixedVectors h
      c A K.toSubgroup hc hv

end Langlands
