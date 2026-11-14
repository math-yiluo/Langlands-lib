import Langlands.AllFieldBZ.Representation.CompactCoefficient.SelectedProjector
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalBlockIsolationStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement IrreducibleQuasicuspidalLeviAdmissibilityTheorem LeviCuspidalBlockIsolationTheorem LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem NonassociatedJacquetSubquotientsTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitInclusion determinantUnitInclusion_apply determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset glCuspidalTensorAssociation isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviCuspidalBlockIsolationTheorem leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.GeneralLinear
open Langlands.CompactCoefficientClass
universe uF uV

/-- Finite-type isolation for every cuspidal irreducible representation of a product Levi. -/
theorem leviCuspidalBlockIsolationTheorem :
    LeviCuspidalBlockIsolationTheorem.{uF, uV} := by
  intro F T n B
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  let N := determinantUnitSubgroup T B
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let μ : MeasureTheory.Measure N := MeasureTheory.Measure.haar
  have hcof : ∀ K : OpenSubgroup N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance N ∅ K
    exact ⟨L, hL, hLK⟩
  have hsplit :
      ∀ (c : CompactCoefficientClass.{uF, uV} N) (X : SmoothRep.{0, uF, uV} ℂ N),
        IsCompl (isotypicSubrepresentation c X).toSubmodule
          (annihilatorSubrepresentation c X).toSubmodule :=
    CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof
  intro A D hD hcusp
  obtain ⟨m, V, hV, hspan⟩ := (FiniteRestriction.leviFiniteRestriction F T B D hD).2
  have hcD : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N D).representation :=
    (leviHarishChandraTheorem F T n B D).mp hcusp.2
  obtain ⟨hsemi, S, Q, hSQ, hS, htypes, hexclude⟩ :=
    finiteFamilyBlockIsolation_of_isCompl N μ hsplit A D hD hcD V hV hspan
  exact ⟨hsemi, m, V, hV, hspan, S, Q, hSQ, hS, htypes, hexclude⟩

end Langlands.AllFieldBZ.CuspidalSupport
