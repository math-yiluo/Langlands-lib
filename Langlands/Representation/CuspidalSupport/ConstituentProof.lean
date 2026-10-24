import Langlands.Representation.CuspidalSupport.ConstituentRankZero
import Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes
import Langlands.Representation.CuspidalSupport.ConstituentComplement
import Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! Actual embeddings and quotients for cuspidal constituents of admissible Levis. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear SmoothRep

universe uF uV

/-- The full cuspidal constituent theorem, including rank zero and independent
field and representation-carrier universes. -/
theorem leviCuspidalConstituentTheorem {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviCuspidalConstituentTheorem.{uF, uV} F T B := by
  by_cases hn : n = 0
  · subst n
    exact leviCuspidalConstituent_rankZero F T B
  let := T.topology
  let := T.leviNonarchimedean B
  let := T.leviLocallyCompactSpace B
  let H := determinantUnitOpenSubgroup T B
  let : H.toSubgroup.Normal := determinantUnitSubgroup_normal T B
  let : (H.toSubgroup ⊔ Subgroup.center (B.Levi F.Carrier)).FiniteIndex :=
    determinantUnit_sup_center_finiteIndex T B
  intro A D hAa hDi hDc hDA
  obtain ⟨_, m, V, hV, _, S, Q, hSQ, hS, htypes, hQ⟩ :=
    leviCuspidalBlockIsolationTheorem p F T n B A D hDi hDc
  have hDS := irreducibleSubquotient_of_isCompl S Q hSQ hDi hDA hQ
  have hSa : (subrepresentation A S).IsAdmissible :=
    isAdmissible_of_injective (hom (subtype A S)) (subtype_injective A S) hAa
  have hVne (i : Fin m) : V i ≠ ⊥ := by
    let := hV i
    let : Nontrivial (V i).toSubmodule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (determinantUnitSubgroup T B))
        (V i).toRepresentation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : (V i).toSubmodule)
    intro heq
    have hz : (v : D) ∈ (⊥ : Subrepresentation
        (determinantUnitRestriction T B D.representation)) := heq ▸ v.property
    exact hv (Subtype.ext hz)
  have hSD : IsSubrepresentation D (subrepresentation A S) ∧
      IsQuotient D (subrepresentation A S) := by
    apply constituent_of_finite_types H (subrepresentation A S) D hSa hS
      hDc.1 hDi V hVne
    · intro W hW
      obtain ⟨i, ⟨e⟩⟩ := htypes W
        (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom W hW)
      exact ⟨i, ⟨e.symm⟩⟩
    · exact hDS
  exact constituent_of_isCompl S Q hSQ hSD

end Langlands.CuspidalSupport
