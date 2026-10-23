import Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement
import Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
import Langlands.Representation.CompactCoefficient.SelectedAssembly
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Finite-type isolation of a cuspidal constituent on a determinant-unit Levi. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear CompactCoefficientClass

universe uF uV

/-- Finite-type isolation for every cuspidal irreducible representation of a product Levi. -/
theorem leviCuspidalBlockIsolationTheorem :
    LeviCuspidalBlockIsolationTheorem.{uF, uV} := by
  intro p _ F T n B
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
    (leviHarishChandraTheorem p F T n B D).mp hcusp.2
  obtain ⟨hsemi, S, Q, hSQ, hS, htypes, hexclude⟩ :=
    finiteFamilyBlockIsolation_of_isCompl N μ hsplit A D hD hcD V hV hspan
  exact ⟨hsemi, m, V, hV, hspan, S, Q, hSQ, hS, htypes, hexclude⟩

end Langlands.CuspidalSupport
