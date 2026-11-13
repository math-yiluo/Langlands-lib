import Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllField.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement
noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem LeviQuasicuspidalFiniteLengthStatement continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition_of_inputs leviQuasicuspidalFiniteLength levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.AllField.CuspidalSupport

open scoped MonoidAlgebra
open Topology

universe uG uV

namespace QuasicuspidalFiniteLength
open Langlands.CuspidalSupport.QuasicuspidalFiniteLength
open Langlands.AllField.CuspidalSupport.QuasicuspidalFiniteLength
open Langlands.CuspidalSupport hiding DeterminantUnitSmoothDualStatement LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem LeviQuasicuspidalFiniteLengthStatement continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition_of_inputs leviQuasicuspidalFiniteLength levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.AllField.CuspidalSupport

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

section Topological

variable [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

end Topological

end QuasicuspidalFiniteLength

/-- Finitely generated admissible quasicuspidal representations of every actual
standard product Levi have finite group-algebra length. -/
theorem leviQuasicuspidalFiniteLength.{uField, uCarrier} :
    LeviQuasicuspidalFiniteLengthStatement.{uField, uCarrier} := by
  intro F _ T n B
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  let := T.leviNonarchimedean B
  let := T.leviLocallyCompactSpace B
  intro A hAa hAc hAf
  let H := determinantUnitOpenSubgroup T B
  let : (H.toSubgroup ⊔ Subgroup.center (B.Levi F)).FiniteIndex :=
    determinantUnit_sup_center_finiteIndex T B
  let : Module.Finite (MonoidAlgebra ℂ (B.Levi F)) A.representation.asModule := hAf
  obtain ⟨K, _, _, hgen⟩ := QuasicuspidalFiniteLength.exists_fixedVectors_generating
    A.representation A.isSmooth H
  let : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) := hAa.2 K
  let : Module.Finite ℂ[H] (Representation.asModule (A.representation.comp H.toSubgroup.subtype)) :=
    QuasicuspidalFiniteLength.finite_of_fixedVectors_generating
      A.representation H.toSubgroup K.toSubgroup hgen
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  let : TotallySeparatedSpace (determinantUnitSubgroup T B) :=
    NonarchimedeanGroup.instTotallySeparated
  let : TotallyDisconnectedSpace (determinantUnitSubgroup T B) :=
    TotallySeparatedSpace.totallyDisconnectedSpace _
  let : MeasurableSpace (determinantUnitSubgroup T B) := borel _
  let : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  have hss := CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    (MeasureTheory.Measure.haar (G := determinantUnitSubgroup T B))
    (determinantUnitRestriction T B A.representation)
    (isSmooth_determinantUnitRestriction T B A.isSmooth)
    ((leviHarishChandraTheorem F T n B A).mp hAc)
  let : IsSemisimpleModule ℂ[H] (Representation.asModule (A.representation.comp H.toSubgroup.subtype)) :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hss
  apply QuasicuspidalFiniteLength.finiteLength_of_restriction A.representation H.toSubgroup
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end Langlands.AllField.CuspidalSupport
