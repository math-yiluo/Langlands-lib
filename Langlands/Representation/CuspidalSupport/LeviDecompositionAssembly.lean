import Langlands.Group.GL.CompactOpen
import Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
import Langlands.Representation.CuspidalSupport.HarishChandraStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement

/-! Actual determinant-unit topology and conditional Levi decomposition. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Topology Filter CompactCoefficientClass

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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

/-- The ambient Levi projector, conditional only on intrinsic complements and finite strata. -/
def leviCompactProjector :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) →
      A.representation.IntertwiningMap A.representation := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  letI := determinantUnitNonarchimedean T B
  letI := determinantUnitLocallyCompactSpace T B
  exact normalSubgroupProjector (determinantUnitSubgroup T B) hsplit hstrata

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
  · exact (hHC p F T n B (SmoothRep.subrepresentation A S)).mpr hS
  · intro D hD hqc
    exact hQ D hD ((hHC p F T n B D).mp hqc)

end
end Langlands.CuspidalSupport
