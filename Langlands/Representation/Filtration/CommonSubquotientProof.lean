import Langlands.Representation.Filtration.CommonSubquotientStatement

open CategoryTheory

namespace Langlands

universe uK uG uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

theorem sameFactorsCommonSubquotient :
    SameFactorsCommonSubquotientStatement.{uK, uG, uV, uW} (k := k) (G := G) := by
  intro A B hA h
  let : Nontrivial A := hA
  obtain ⟨n, s, t, hs, ht, e, he⟩ := h
  have hn : 0 < n := by
    by_contra hn
    have hn : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hbot : (⊥ : Subrepresentation A.representation) = ⊤ :=
      s.subrepresentation_zero.symm.trans s.subrepresentation_last
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    have hmem : v ∈ (⊥ : Subrepresentation A.representation) := by
      rw [hbot]
      trivial
    exact hv hmem
  let i : Fin n := ⟨0, hn⟩
  refine ⟨s.subrepresentation i.succ,
    (s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit),
    t.subrepresentation (e i).succ,
    (t.step (e i).castSucc).lowerInUpper (t.step (e i).succ) (Discrete.mk PUnit.unit),
    ?_, ?_⟩
  · exact hs i
  · exact he i

end Langlands
