import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.CuspidalSupport.LeviCompactPart

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviCompactPart`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviCompactPart` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust glCuspidalTensorAssociation isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviQuasicuspidalDecomposition_of_inputs mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
open Langlands.CompactCoefficientClass
universe uF uV

variable {F : LocalFieldPackage.{uF}}
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

end Langlands.AllFieldBZ.CuspidalSupport
