/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Continuity of a Kan extension detected by representables

The argument uses the canonical colimit of representables and keeps the actual
comparison map, so it applies to section cocones with their restriction maps.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private noncomputable def colimitEvaluationComparison
    {D : Type (u + 1)} [Category.{u} D]
    {J : Type w} [SmallCategory J] (K : J ⥤ Dᵒᵖ) (c : Cocone K)
    [HasColimitsOfShape J (Type (u + 1))] :
    (Functor.whiskeringLeft J Dᵒᵖ (Type (u + 1))).obj K ⋙ colim ⟶
      (evaluation Dᵒᵖ (Type (u + 1))).obj c.pt where
  app P := colimit.desc (K ⋙ P) (P.mapCocone c)
  naturality P Q f := by
    apply colimit.hom_ext
    intro j
    change colimit.ι (K ⋙ P) j ≫ colim.map (K.whiskerLeft f) ≫
        colimit.desc (K ⋙ Q) (Q.mapCocone c) =
      colimit.ι (K ⋙ P) j ≫ colimit.desc (K ⋙ P) (P.mapCocone c) ≫ f.app c.pt
    simp only [colim_map]
    rw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (f.naturality (c.ι.app j)).symm


/-- A set-valued left Kan extension preserves a colimit if the representables in
its defining image preserve that colimit.
Source: the density theorem for presheaves and commutation of colimits, applied to
the finite-presentation argument in Bhatt--Scholze, Lemma 5.1.1.
(auxiliary; not a blueprint node).

Proof: The canonical map from the colimit of values to the value at the colimit
is natural in a presheaf. Both its source and target preserve presheaf colimits:
Kan extension is a left adjoint, restriction and evaluation compute colimits
pointwise, and colimits commute with colimits. On a representable the Kan
extension is the representable of its image, so the given hypothesis makes this
map invertible. Express an arbitrary presheaf as the canonical colimit of its
representables. Preservation of that colimit makes the same map invertible for
the arbitrary presheaf. This is exactly the preservation criterion. -/
theorem lan_preserves_colimit_of_representables
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (B : C ⥤ D) (G : Cᵒᵖ ⥤ Type (u + 1))
    {J : Type u} [SmallCategory J] (K : J ⥤ Dᵒᵖ) (c : Cocone K) (hc : IsColimit c)
    (h : ∀ Y, PreservesColimit K (uliftYoneda.{u + 1}.obj (B.obj Y))) :
    PreservesColimit K (B.op.lan.obj G) := by
  have : PreservesColimitsOfSize.{u, u + 1}
      (B.op.lan : (Cᵒᵖ ⥤ Type (u + 1)) ⥤ Dᵒᵖ ⥤ Type (u + 1)) :=
    (B.op.lanAdjunction (Type (u + 1))).leftAdjoint_preservesColimits
  let a := colimitEvaluationComparison K c
  let a' := Functor.whiskerLeft B.op.lan a
  have hrep (Y : C) : IsIso (a.app (uliftYoneda.{u + 1}.obj (B.obj Y))) := by
    let := h Y
    change IsIso (colimit.desc (K ⋙ uliftYoneda.{u + 1}.obj (B.obj Y))
      ((uliftYoneda.{u + 1}.obj (B.obj Y)).mapCocone c))
    change IsIso (((colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitOfPreserves (uliftYoneda.{u + 1}.obj (B.obj Y)) hc)).hom)
    infer_instance
  have happ (Y : C) : IsIso (a'.app (uliftYoneda.{u + 1}.obj Y)) := by
    let e := (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1} B).app Y
    have : IsIso (a.app (uliftYoneda.{u + 1}.obj (B.obj Y))) := hrep Y
    have eq : a'.app (uliftYoneda.{u + 1}.obj Y) =
        (((Functor.whiskeringLeft J Dᵒᵖ (Type (u + 1))).obj K ⋙ colim).map e.inv) ≫
          a.app (uliftYoneda.{u + 1}.obj (B.obj Y)) ≫
            ((evaluation Dᵒᵖ (Type (u + 1))).obj c.pt).map e.hom := by
      change a.app _ = _
      rw [← a.naturality, ← Functor.map_comp_assoc]
      rw [e.inv_hom_id, Functor.map_id, Category.id_comp]
      rfl
    rw [eq]
    infer_instance
  have : IsIso (Functor.whiskerLeft (Presheaf.functorToRepresentables.{u + 1} G) a') := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    exact happ i.unop.1.unop
  have : IsIso (a'.app G) := isIso_app_coconePt_of_preservesColimit
    (Presheaf.functorToRepresentables.{u + 1} G) a' (Presheaf.coconeOfRepresentable.{u + 1} G)
      (Presheaf.colimitOfRepresentable.{u + 1} G)
  have : IsIso (colimit.desc (K ⋙ B.op.lan.obj G)
      ((B.op.lan.obj G).mapCocone c)) := by exact this
  have : IsIso ((colimit.isColimit (K ⋙ B.op.lan.obj G)).desc
      ((B.op.lan.obj G).mapCocone c)) := by exact this
  exact preservesColimit_of_preserves_colimit_cocone hc
    (IsColimit.ofPointIso (colimit.isColimit (K ⋙ B.op.lan.obj G)))

end CategoryTheory
