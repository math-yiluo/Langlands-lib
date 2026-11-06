import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Open pieces of colimits of locally ringed spaces -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry Topology

universe u v w

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PresheafedColimit

variable {J : Type v} [Category.{w} J]
variable {C : Type (u + 1)} [Category.{u} C]
variable [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ C]
variable {F G : J ⥤ PresheafedSpace.{u, u + 1, u} C} (τ : F ⟶ G)

lemma preimage_colimMap (V : Opens (colimit G).carrier) (j : J) :
    (Opens.map (τ.app j).base).obj ((Opens.map (colimit.ι G j).base).obj V) =
      (Opens.map (colimit.ι F j).base).obj ((Opens.map (colim.map τ).base).obj V) := by
  rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base,
    ← colimit.ι_map, PresheafedSpace.comp_base, Opens.map_comp_obj]

/-- The sectionwise comparison induced by a map of diagrams. -/
def componentwiseMap (V : Opens (colimit G).carrier) :
    PresheafedSpace.componentwiseDiagram G V ⟶
      PresheafedSpace.componentwiseDiagram F ((Opens.map (colim.map τ).base).obj V) where
  app j := (τ.app (unop j)).c.app (op ((Opens.map (colimit.ι G (unop j)).base).obj V)) ≫
    (F.obj (unop j)).presheaf.map (eqToHom (congrArg op (preimage_colimMap τ V (unop j))))
  naturality {j k} f := by
    dsimp [PresheafedSpace.componentwiseDiagram]
    have hn := PresheafedSpace.congr_app (τ.naturality f.unop) (op
      ((Opens.map (colimit.ι G (unop j)).base).obj V))
    simp only [PresheafedSpace.comp_c_app] at hn
    simp only [Category.assoc, NatTrans.naturality_assoc]
    rw [reassoc_of% hn]
    dsimp only [TopCat.Presheaf.pushforward_obj_map]
    simp only [← (F.obj (unop k)).presheaf.map_comp]
    congr 1

lemma colimMap_app_componentwiseMap (V : Opens (colimit G).carrier) :
    (colim.map τ).c.app (op V) ≫
        (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit F
          ((Opens.map (colim.map τ).base).obj V)).hom =
      (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit G V).hom ≫
        lim.map (componentwiseMap τ V) := by
  apply limit.hom_ext
  rintro ⟨j⟩
  rw [Category.assoc,
    PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π,
    Category.assoc, limit.map_π]
  rw [← Category.assoc,
    PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  dsimp only [componentwiseMap, unop_op]
  rw [← PresheafedSpace.comp_c_app, PresheafedSpace.congr_app (colimit.ι_map τ j)]
  simp only [PresheafedSpace.comp_c_app, Category.assoc]

/-- If the section maps of a diagram comparison are isomorphisms over an open of
its target colimit, the induced map on colimit sections is an isomorphism. -/
lemma isIso_colimMap_app (V : Opens (colimit G).carrier)
    (h : ∀ j, IsIso ((τ.app j).c.app
      (op ((Opens.map (colimit.ι G j).base).obj V)))) :
    IsIso ((colim.map τ).c.app (op V)) := by
  have : ∀ j, IsIso ((componentwiseMap τ V).app j) := fun j => by
    have := h (unop j)
    dsimp [componentwiseMap]
    infer_instance
  have : IsIso (componentwiseMap τ V) := NatIso.isIso_of_isIso_app _
  have he := colimMap_app_componentwiseMap τ V
  rw [← Iso.eq_comp_inv] at he
  rw [he]
  infer_instance

/-- An open saturated comparison of diagrams induces an open immersion on colimits. -/
lemma isOpenImmersion_colimMap
    [hτ : ∀ j, PresheafedSpace.IsOpenImmersion (τ.app j)]
    (hopen : IsOpenEmbedding (colim.map τ).base)
    (hsat : ∀ j, Set.range (τ.app j).base =
      (colimit.ι G j).base ⁻¹' Set.range (colim.map τ).base) :
    PresheafedSpace.IsOpenImmersion (colim.map τ) where
  base_open := hopen
  c_iso U := by
    apply isIso_colimMap_app τ
    intro j
    let V := (Opens.map (colimit.ι G j).base).obj (hopen.functor.obj U)
    have hV : (V : Set (G.obj j)) ⊆ Set.range (τ.app j).base := by
      intro x hx
      rw [hsat j]
      change (colimit.ι G j).base x ∈ Set.range (colim.map τ).base
      change (colimit.ι G j).base x ∈ (colim.map τ).base '' (U : Set (colim.obj F).carrier) at hx
      rcases hx with ⟨z, hz, heq⟩
      exact ⟨z, heq⟩
    apply PresheafedSpace.IsOpenImmersion.c_iso' (τ.app j)
      ((Opens.map (τ.app j).base).obj V)
    apply SetLike.coe_injective
    change (V : Set (G.obj j)) = (τ.app j).base '' ((τ.app j).base ⁻¹' (V : Set (G.obj j)))
    exact (Set.image_preimage_eq_of_subset hV).symm

end PresheafedColimit

end Langlands.AlgebraicGeometry.IntegralSchemePushout
