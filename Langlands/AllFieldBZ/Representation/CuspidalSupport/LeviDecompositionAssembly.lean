import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.CompactCoefficient.NormalSubgroupDecomposition
import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitInclusion determinantUnitInclusion_apply determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal glCuspidalTensorAssociation isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviQuasicuspidalDecomposition_of_inputs mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
open Topology
open Filter
open Langlands.CompactCoefficientClass
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The actual determinant-unit subgroup is nonarchimedean in its subtype topology. -/
theorem determinantUnitNonarchimedean :
    letI := T.topology
    NonarchimedeanGroup (determinantUnitSubgroup T B) := by
  let := T.topology
  let := T.leviNonarchimedean B
  refine { is_nonarchimedean := ?_ }
  intro U hU
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨K, hK⟩ :=
    NonarchimedeanGroup.is_nonarchimedean (G := B.Levi F.Carrier) V hV
  exact ⟨OpenSubgroup.comap (determinantUnitSubgroup T B).subtype
    continuous_subtype_val K, fun x hx => hVU (hK hx)⟩

/-- Openness in the locally compact actual Levi supplies local compactness. -/
theorem determinantUnitLocallyCompactSpace :
    letI := T.topology
    LocallyCompactSpace (determinantUnitSubgroup T B) := by
  let := T.topology
  let := T.leviLocallyCompactSpace B
  exact (isOpen_determinantUnitSubgroup T B).locallyCompactSpace

section
variable (hsplit :
    letI := T.topology
    ∀ (c : CompactCoefficientClass.{uF, uV} (determinantUnitSubgroup T B))
      (D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B)),
      IsCompl (isotypicSubrepresentation c D).toSubmodule
        (annihilatorSubrepresentation c D).toSubmodule)
  (hstrata :
    letI := T.topology
    ∀ K : OpenSubgroup (determinantUnitSubgroup T B),
      IsCompact (K : Set (determinantUnitSubgroup T B)) →
        (fixedStratum.{uF, uV} K.toSubgroup).Finite)

include hsplit hstrata in
/-- The exact published Levi decomposition follows from the four analytic
inputs and Harish-Chandra's criterion. No additional topology is assumed. -/
theorem leviQuasicuspidalDecomposition_of_inputs
    (hcompact :
      letI := T.topology
      ∀ D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B),
        HasCompactSmoothDualCoefficients
          (totalIsotypicSubrepresentation.{uF, uV} D).toRepresentation)
    (hexhaust :
      letI := T.topology
      ∀ D : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B),
        HasCompactSmoothDualCoefficients D.representation →
          totalIsotypicSubrepresentation.{uF, uV} D = ⊤)
    (hHC : LeviHarishChandraTheorem.{uF, uV}) :
    LeviQuasicuspidalDecompositionTheorem.{uF, uV} F T B := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  intro A
  obtain ⟨S, Q, hSQ, hS, hQ⟩ :=
    decomposition_of_normalSubgroup_compactCoefficients
      (determinantUnitSubgroup T B) hsplit hstrata hcompact hexhaust A
  refine ⟨S, Q, hSQ, ?_, ?_⟩
  · exact (hHC F T n B (SmoothRep.subrepresentation A S)).mpr hS
  · intro D hD hqc
    exact hQ D hD ((hHC F T n B D).mp hqc)

end
end Langlands.AllFieldBZ.CuspidalSupport
