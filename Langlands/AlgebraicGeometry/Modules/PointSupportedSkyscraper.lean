import Langlands.AlgebraicGeometry.Modules.StalkAdjunction
import Langlands.AlgebraicGeometry.Modules.ModuleSupport

/-! # Modules supported at one closed point are skyscrapers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.StalkAdjunction

variable {X : Scheme.{u}} (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))

/-- Skyscraper sections over an open not containing the point form a subsingleton. -/
lemma subsingleton_sections_of_not_mem {U : X.Opens} (hx : x ∉ U) :
    Subsingleton ((skyscraper x N).presheaf.obj (op U)) := by
  have : IsEmpty (PLift (x ∈ U)) := ⟨fun h ↦ hx h.down⟩
  exact inferInstanceAs (Subsingleton (sections x N U))

/-- A skyscraper stalk vanishes at every point that is not a specialization of the
skyscraper point. -/
lemma subsingleton_stalk_of_not_specializes {y : X} (h : ¬ x ⤳ y) :
    Subsingleton ((skyscraper x N).presheaf.stalk y) := by
  rw [specializes_iff_forall_open] at h
  push Not at h
  obtain ⟨s, hs, hys, hxs⟩ := h
  refine ⟨fun a b ↦ ?_⟩
  suffices H : ∀ c : (skyscraper x N).presheaf.stalk y, c = 0 by rw [H a, H b]
  intro c
  obtain ⟨U, hyU, c, rfl⟩ := (skyscraper x N).presheaf.exists_germ_eq c
  let V : X.Opens := U ⊓ ⟨s, hs⟩
  have hyV : y ∈ V := ⟨hyU, hys⟩
  have hxV : x ∉ V := fun h ↦ hxs h.2
  have := subsingleton_sections_of_not_mem x N hxV
  rw [← (skyscraper x N).presheaf.germ_res_apply (homOfLE inf_le_left) y hyV c,
    Subsingleton.elim ((skyscraper x N).presheaf.map (homOfLE inf_le_left).op c) 0, map_zero]

/-- Evaluation at the point is injective on the skyscraper stalk at that point. -/
lemma fromStalkAdd_id_injective :
    Function.Injective (fromStalkAdd x (𝟙 (skyscraper x N))) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨U, hxU, c, rfl⟩ := (skyscraper x N).presheaf.exists_germ_eq c
  rw [fromStalkAdd_germ] at hc
  have hc0 : c = 0 := by
    funext hx
    exact hc
  rw [hc0, map_zero]

variable {x}

/-- A module whose stalk support lies in a closed point is the skyscraper of its stalk:
the unit of the stalk-skyscraper adjunction is an isomorphism. -/
theorem isIso_unit_app_of_stalkSupport_subset (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (hM : stalkSupport M ⊆ {x}) : IsIso ((adjunction x).unit.app M) := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := SheafOfModules.toSheaf X.ringCatSheaf
  have : F.ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms
  let η := (adjunction x).unit.app M
  suffices IsIso (F.map η) from isIso_of_reflects_iso η F
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro y
  rw [ConcreteCategory.isIso_iff_bijective]
  by_cases hy : y = x
  · subst hy
    let s := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map (F.map η).1
    let e := fromStalkAdd y (𝟙 (skyscraper y ((stalkFunctor y).obj M)))
    have he : ∀ m, e (s m) = m := by
      intro m
      obtain ⟨U, hyU, m, rfl⟩ := M.presheaf.exists_germ_eq m
      change e ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map (F.map η).1
        (M.presheaf.germ U y hyU m)) = _
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      erw [fromStalkAdd_germ]
      rfl
    have hinj := fromStalkAdd_id_injective y ((stalkFunctor y).obj M)
    refine ⟨fun a b hab ↦ by rw [← he a, ← he b]; exact congrArg e hab, fun c ↦ ⟨e c, ?_⟩⟩
    exact hinj (he (e c))
  · have hnot : ¬ x ⤳ y := by
      rw [specializes_iff_mem_closure, hx.closure_eq]
      exact fun h ↦ hy h
    have h1 : Subsingleton (M.presheaf.stalk y) := by
      have : y ∉ stalkSupport M := fun h ↦ hy (hM h)
      rw [mem_stalkSupport_iff_nontrivial, not_nontrivial_iff_subsingleton] at this
      exact this
    have h2 := subsingleton_stalk_of_not_specializes x ((stalkFunctor x).obj M) hnot
    exact ⟨fun a b _ ↦ @Subsingleton.elim _ h1 a b, fun c ↦ ⟨0, @Subsingleton.elim _ h2 _ _⟩⟩

/-- A module whose stalk support lies in a closed point is isomorphic to the skyscraper of its
stalk at that point. -/
def isoSkyscraperOfStalkSupportSubset (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (hM : stalkSupport M ⊆ {x}) : M ≅ skyscraper x ((stalkFunctor x).obj M) :=
  haveI := isIso_unit_app_of_stalkSupport_subset hx M hM
  asIso ((adjunction x).unit.app M)

/-- For a module whose stalk support lies in a closed point, the germ at that point is bijective
on sections over every open neighbourhood of the point. -/
theorem germ_bijective_of_stalkSupport_subset (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (hM : stalkSupport M ⊆ {x}) (U : X.Opens) (hxU : x ∈ U) :
    Function.Bijective (M.presheaf.germ U x hxU) := by
  have := isIso_unit_app_of_stalkSupport_subset hx M hM
  let η := (adjunction x).unit.app M
  have hη : IsIso (η.app U) :=
    inferInstanceAs (IsIso (((Scheme.Modules.toPresheaf X).map η).app (op U)))
  have heq : ⇑(M.presheaf.germ U x hxU) =
      (sectionsIso x ((stalkFunctor x).obj M) U hxU).hom ∘ η.app U := by
    funext m
    rfl
  rw [heq]
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp
    ((ConcreteCategory.isIso_iff_bijective _).1 hη)

end Langlands.AlgebraicGeometry.Modules.StalkAdjunction
