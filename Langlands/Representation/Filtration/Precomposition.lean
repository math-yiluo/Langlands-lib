import Langlands.Representation.Filtration.Transport

/-! Natural graded comparisons and gluing under precomposition of inputs. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC uD vD

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ Rep.{uV} R G} {n : ℕ}

namespace RepFunctorFiltration

/-- The actual quotient functors commute naturally with precomposition. -/
def precompGradedIso (s : RepFunctorFiltration F n) (J : D ⥤ C) (i : Fin n) :
    (s.precomp J).graded i ≅ J ⋙ s.graded i :=
  eqToIso (by rfl)

/-- Keep every supplied natural grade identification after precomposition. -/
theorem HasGradedPieces.precomp {s : RepFunctorFiltration F n}
    {pieces : Fin n → C ⥤ Rep.{uV} R G} (h : s.HasGradedPieces pieces)
    (J : D ⥤ C) :
    (s.precomp J).HasGradedPieces (fun i => J ⋙ pieces i) := by
  intro i
  obtain ⟨e⟩ := h i
  exact ⟨s.precompGradedIso J i ≪≫ Functor.isoWhiskerLeft J e⟩

end RepFunctorFiltration

variable {pieces : Fin n → C ⥤ Rep.{uV} R G}

/-- Precomposition preserves the full ordered family of actual grades. -/
theorem HasOrderedFiltration.precomp (h : HasOrderedFiltration F pieces)
    (J : D ⥤ C) : HasOrderedFiltration (J ⋙ F) (fun i => J ⋙ pieces i) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s.precomp J, hs.precomp J⟩

/-- Precomposition preserves gluing and its witnessing permutation. -/
theorem IsGluedFrom.precomp (h : IsGluedFrom F pieces) (J : D ⥤ C) :
    IsGluedFrom (J ⋙ F) (fun i => J ⋙ pieces i) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he.precomp J⟩

end Langlands
