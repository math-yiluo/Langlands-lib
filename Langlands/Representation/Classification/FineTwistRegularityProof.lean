import Langlands.Representation.Classification.FineTwistRegularityStatement
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! Actual real-twist preservation and the fine-subgroup specialization. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Every actual refined unipotent radical lies in the real character kernel. -/
theorem refinedUnipotent_le_ker_leviRealPowerCharacter
    (S : BlockRefinement B) (s : Fin B.length → ℝ) :
    refinedUnipotent F.Carrier B S ≤ (T.leviRealPowerCharacter B s).ker := by
  intro g hg
  change T.leviRealPowerCharacter B s g = 1
  rw [T.leviRealPowerCharacter_apply]
  apply Finset.prod_eq_one
  intro i _
  have hdet := (S i).determinant_eq_one_of_mem_unipotentSubgroup
    ((mem_refinedUnipotent F.Carrier B S g).mp hg i)
  simp [realPowerCharacter, determinantNorm, hdet]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem isAdmissible_leviRealPowerTwist_iff (s : Fin B.length → ℝ)
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    let := T.topology
    IsAdmissible (T.leviRealPowerTwist B s ρ) ↔ IsAdmissible ρ := by
  let := T.topology
  exact isAdmissible_twist_iff _ ρ (T.isOpen_ker_leviRealPowerCharacter B s)

theorem isIrreducible_leviRealPowerTwist_iff (s : Fin B.length → ℝ)
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation.IsIrreducible (T.leviRealPowerTwist B s ρ) ↔
      Representation.IsIrreducible ρ :=
  isIrreducible_twist_iff _ ρ

theorem isLeviQuasicuspidal_leviRealPowerTwist_iff (s : Fin B.length → ℝ)
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    CuspidalSupport.IsLeviQuasicuspidal B (T.leviRealPowerTwist B s ρ) ↔
      CuspidalSupport.IsLeviQuasicuspidal B ρ := by
  unfold CuspidalSupport.IsLeviQuasicuspidal
  exact forall_congr' fun S => forall_congr' fun _ =>
    Jacquet.subsingleton_coinvariants_twist_iff _ ρ
      (T.refinedUnipotent_le_ker_leviRealPowerCharacter B S s)

theorem isLeviCuspidal_leviRealPowerTwist_iff (s : Fin B.length → ℝ)
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    let := T.topology
    CuspidalSupport.IsLeviCuspidal B (T.leviRealPowerTwist B s ρ) ↔
      CuspidalSupport.IsLeviCuspidal B ρ := by
  let := T.topology
  exact and_congr (T.isAdmissible_leviRealPowerTwist_iff B s ρ)
    (T.isLeviQuasicuspidal_leviRealPowerTwist_iff B s ρ)

end PadicField.TopologicalData

/-- The fine action is transported along the actual flattened-Levi equivalence. -/
theorem fineTwistIrreducibleAdmissible :
    FineTwistIrreducibleAdmissibleStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro n B S ω hωirr hωcusp v₀ t
  let s : Fin (B.flatten S).length → ℝ :=
    fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1
  let ρ := T.leviRealPowerTwist (B.flatten S) s ω.ρ
  have hρirr : Representation.IsIrreducible ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) s ω.ρ).mpr hωirr
  have hρcusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) s ω.ρ).mpr hωcusp
  refine ⟨?_, ?_, hρcusp⟩
  · exact (CuspidalSupport.isIrreducible_comp_mulEquiv_iff ρ
      (flattenedLeviEquiv F.Carrier B S).symm).mpr hρirr
  · exact isAdmissible_comp_continuousMulEquiv ρ
      (flattenedLeviEquivContinuous F.Carrier B S).symm hρcusp.1

/-- The exact closed regularity family, preserving independent field/carrier universes. -/
theorem fineTwistRegularity : FineTwistRegularityStatement.{uF, uV} := by
  refine ⟨?_, ?_, ?_, fineTwistIrreducibleAdmissible⟩
  · intro p _ F T
    let := T.topology
    intro n B V _ _ ρ s
    exact T.isLeviCuspidal_leviRealPowerTwist_iff B s ρ
  · intro p _ F T
    let := T.topology
    intro n B V _ _ ρ s
    exact T.isAdmissible_leviRealPowerTwist_iff B s ρ
  · intro p _ F T n B V _ _ ρ s
    exact T.isIrreducible_leviRealPowerTwist_iff B s ρ

end Langlands
