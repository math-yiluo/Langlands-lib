import Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement
import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.KPDoubleRootFiltrationExistence

/-! # Existence of the KP §9.8 filtration of `Z(F)` -/

universe u

namespace Langlands.Geometry.Building

/-- The double-root existence statement (KP Lemma 9.8.1 with the sharper `2r` bound) implies
the plain existence statement: drop the conjunct `IsDoubleRootCommutatorFriendly`. -/
theorem centralizerFiltrationExistence_of_doubleRoot
    (h : CentralizerFiltrationDoubleRootExistenceStatement.{u}) :
    CentralizerFiltrationExistenceStatement.{u} := by
  intro F _ _ _ _ G _ P hP
  obtain ⟨Zf, hax, hopen, -⟩ := h F G P hP
  exact ⟨Zf, hax, hopen⟩

/-- **Existence of the KP §9.8 filtration of `Z(F)`** (KP §9.8, Lemma 9.8.1). Every parahoric
building datum satisfying the apartment axioms has a centralizer filtration that satisfies the
filtration axioms and is open. It is the filtration of the published double-root existence
theorem `centralizerFiltrationDoubleRootExistence`, with its extra double-root property
forgotten. -/
theorem centralizerFiltrationExistence : CentralizerFiltrationExistenceStatement.{u} :=
  centralizerFiltrationExistence_of_doubleRoot centralizerFiltrationDoubleRootExistence

end Langlands.Geometry.Building
