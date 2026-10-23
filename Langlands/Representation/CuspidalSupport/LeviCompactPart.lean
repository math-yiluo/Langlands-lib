import Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Compactness and exhaustion for the actual determinant-unit subgroup. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear CompactCoefficientClass

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Compact open subgroups of the actual determinant-unit subgroup are cofinal. -/
theorem determinantUnitCompactOpenCofinal :
    letI := T.topology
    ∀ K : OpenSubgroup (determinantUnitSubgroup T B),
      ∃ L : OpenSubgroup (determinantUnitSubgroup T B),
        IsCompact (L : Set (determinantUnitSubgroup T B)) ∧ L ≤ K := by
  let := T.topology
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  intro K
  obtain ⟨L, hL, hLK⟩ := compactOpenSubgroupBasis (determinantUnitSubgroup T B)
    (K : Set (determinantUnitSubgroup T B)) (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L, hL, hLK⟩

/-- The total intrinsic isotypic part of an actual determinant-unit representation
has compact smooth-dual coefficients. -/
theorem determinantUnitTotalIsotypic_compact :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B),
      HasCompactSmoothDualCoefficients
        (totalIsotypicSubrepresentation.{uF, uV} D).toRepresentation := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients
    (determinantUnitCompactOpenCofinal T B)

/-- Every compact-coefficient actual determinant-unit representation is
exhausted by the intrinsic total isotypic part. -/
theorem determinantUnitTotalIsotypic_exhaust :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B),
      HasCompactSmoothDualCoefficients D.representation →
        totalIsotypicSubrepresentation.{uF, uV} D = ⊤ := by
  let := T.topology
  let := T.leviT2Space B
  let := T.leviTopologicalGroup B
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  let : T2Space (determinantUnitSubgroup T B) := inferInstance
  let : TotallySeparatedSpace (determinantUnitSubgroup T B) :=
    NonarchimedeanGroup.instTotallySeparated
  let : TotallyDisconnectedSpace (determinantUnitSubgroup T B) :=
    TotallySeparatedSpace.totallyDisconnectedSpace _
  let : MeasurableSpace (determinantUnitSubgroup T B) :=
    borel (determinantUnitSubgroup T B)
  let : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  exact totalIsotypicSubrepresentation_eq_top_of_compactCoefficients
    (MeasureTheory.Measure.haar (G := determinantUnitSubgroup T B))

/-- Intrinsic isotypic and annihilator parts are complementary for every
smooth representation of the actual determinant-unit subgroup. -/
theorem determinantUnitIsotypic_isCompl :
    letI := T.topology
    ∀ (c : CompactCoefficientClass.{uF, uV} (determinantUnitSubgroup T B))
      (D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B)),
      IsCompl (isotypicSubrepresentation c D).toSubmodule
        (annihilatorSubrepresentation c D).toSubmodule := by
  let := T.topology
  let := T.leviT2Space B
  let := T.leviTopologicalGroup B
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  let : T2Space (determinantUnitSubgroup T B) := inferInstance
  let : TotallySeparatedSpace (determinantUnitSubgroup T B) :=
    NonarchimedeanGroup.instTotallySeparated
  let : TotallyDisconnectedSpace (determinantUnitSubgroup T B) :=
    TotallySeparatedSpace.totallyDisconnectedSpace _
  let : MeasurableSpace (determinantUnitSubgroup T B) :=
    borel (determinantUnitSubgroup T B)
  let : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  exact CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
    (MeasureTheory.Measure.haar (G := determinantUnitSubgroup T B))
    (determinantUnitCompactOpenCofinal T B)

end Langlands.CuspidalSupport
