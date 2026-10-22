import Langlands.AlgebraicGeometry.Modules.SectionLocusStatements

/-! # Stalk and maximality comparisons for the section trivialization locus -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- A morphism of scheme modules is an isomorphism iff all its stalk maps are. -/
theorem isIso_iff_stalk_isIso {N P : X.Modules} (φ : N ⟶ P) :
    IsIso φ ↔ ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
      ((Scheme.Modules.toPresheaf X).map φ)) := by
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨P.presheaf, P.isSheaf⟩
  let ψ : F ⟶ G := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  have h : IsIso ψ ↔ IsIso φ :=
    (isIso_iff_of_reflects_iso ψ (TopCat.Sheaf.forget Ab X)).symm.trans
      (isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf X))
  exact h.symm.trans (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso ψ)

/-- Restriction to an open subscheme does not change the stalk maps of a morphism. -/
theorem isIso_stalk_restrict_iff {N P : X.Modules} (φ : N ⟶ P) (U : X.Opens) (y : U.toScheme) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
      ((Scheme.Modules.toPresheaf U).map ((Scheme.Modules.restrictFunctor U.ι).map φ))) ↔
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (U.ι y)).map
      ((Scheme.Modules.toPresheaf X).map φ)) :=
  NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y) φ

/-- A section trivializes on an open precisely when its stalk maps there are isomorphisms. -/
theorem localStalkCriterion : LocalStalkCriterion.{u} := by
  intro X M s U
  unfold TrivializesOn
  rw [isIso_iff_stalk_isIso]
  simp only [isIso_stalk_restrict_iff]
  exact ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h y ↦ h y.1 y.2⟩

/-- Every point of the trivialization open is a stalk frame. -/
theorem isStalkFrame_of_mem_trivializationOpen (M : X.Modules) (s : GlobalSections M) {x : X}
    (hx : x ∈ trivializationOpen M s) : IsStalkFrame M s x := by
  obtain ⟨V, hV, hxV⟩ := (TopologicalSpace.Opens.mem_sSup).mp hx
  exact (localStalkCriterion X M s V).mp hV x hxV

/-- The section trivializes precisely on the subopens of its trivialization open. -/
theorem maximalTrivialization : MaximalTrivialization.{u} := by
  intro X M s U
  refine ⟨fun h ↦ le_sSup h, fun h ↦ ?_⟩
  exact (localStalkCriterion X M s U).mpr fun x hx ↦
    isStalkFrame_of_mem_trivializationOpen M s (h hx)

/-- The trivialization open is the interior of the stalk-frame locus. -/
theorem trivializationOpenInterior : TrivializationOpenInterior.{u} := by
  intro X M s
  apply le_antisymm
  · exact interior_maximal (fun x hx ↦ isStalkFrame_of_mem_trivializationOpen M s hx)
      (trivializationOpen M s).isOpen
  · let W : X.Opens := ⟨interior {x | IsStalkFrame M s x}, isOpen_interior⟩
    have hW : TrivializesOn M s W :=
      (localStalkCriterion X M s W).mpr fun x hx ↦
        (interior_subset hx : x ∈ {x | IsStalkFrame M s x})
    exact (maximalTrivialization X M s W).mp hW

/-- The stalk, interior and maximality comparisons for a section's trivialization locus. -/
theorem sectionLocusComparison : SectionLocusComparison.{u} :=
  ⟨localStalkCriterion, trivializationOpenInterior, maximalTrivialization⟩

end Langlands.SchemeModule
