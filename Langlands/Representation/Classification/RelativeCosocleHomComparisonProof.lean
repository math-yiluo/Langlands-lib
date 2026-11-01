import Langlands.Representation.Exponents.WholeInductionGeometricIsolation
import Langlands.Representation.Classification.RelativeCosocleHomIsolationReduction
import Langlands.Representation.Geometric.RelativeLeadingCharacterExclusionProof
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! The finite-dimensional relative Hom comparison for every actual outer quotient. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeCosocleHomIsolationReduction

universe uF uV uM uW uZ

/-- The actual geometric filtration, tempered leading-character exclusion and
finite-length induction construct the whole-induction leading real block. -/
theorem Exponents.wholeInductionLeadingRealBlock :
    Exponents.WholeInductionLeadingRealBlockStatement.{uF, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B π hπ htemp t ht
  obtain ⟨i, r, hri, hir⟩ :=
    WholeInductionGeometricIsolation.wholeRetractionOfGeometricInputs T B
      relativeGeometricLeadingCharacterExclusion
      (Geometric.padicGeometricLemma p F T n hn B B.reverse)
      hn π hπ htemp t ht
      (temperedInductionFiniteGeneration p F T n hn B π hπ htemp t ht)
  exact ⟨i, r, hri, fun χ _ hre v hv => hir χ hre v hv⟩

/-- The actual fine opposite-Jacquet Hom spaces of any irreducible outer
quotient and its tempered input are finite dimensional with equal finrank. -/
theorem relativeCosocleHomComparison :
    GLRelativeCosocleHomComparisonStatement.{uF, uV, uM, uW, uZ} :=
  comparisonOfIsolationAndFiniteGeneration
    Exponents.wholeInductionLeadingRealBlock temperedInductionFiniteGeneration

end Langlands
