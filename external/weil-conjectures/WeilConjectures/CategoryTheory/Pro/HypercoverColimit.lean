/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Pro.Basic

/-!
# Sections over a limit of hypercovers

Let `E` be a pre-`1`-hypercover of `X : D` presented as a cofiltered limit of pre-`1`-hypercovers
`Eⱼ` of objects `Xⱼ` in the image of `F : C ⥤ D`. If a presheaf `P` sends the presentations of
the components of `E` to colimits and satisfies the sheaf condition both for `E` and for all the
`Eⱼ`, then `P(X)` is the filtered colimit of the `P(Xⱼ)`: filtered colimits commute with the
finite limits expressing the sheaf conditions.

This is a converse to `CategoryTheory.PreOneHypercover.RelativeLimitPresentation.isLimit`, which
deduces the sheaf condition for `E` from the colimit property at `X`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  {J : Type*} [Category J] {X : D} {F : C ⥤ D} {E : PreOneHypercover X}

/-- If `P` satisfies the sheaf condition for a presented pre-`1`-hypercover `E` and for all its
finite stages, and sends the presentations of the components of `E` to colimits, then `P`
sends the presentation of `X` to a colimit. -/
noncomputable def PreOneHypercover.RelativeLimitPresentation.isColimitOfIsLimit (P : Dᵒᵖ ⥤ A)
    [HasColimitsOfShape Jᵒᵖ A]
    [PreservesLimitsOfShape (WalkingMulticospan E.multicospanShape) (colim : (Jᵒᵖ ⥤ A) ⥤ _)]
    (pres : E.RelativeLimitPresentation J F)
    (hE : IsLimit (E.multifork P))
    (h₀ : ∀ i, IsColimit (P.mapCocone (pres.pres₀ i).cone.op))
    (h₁ : ∀ {i j : E.I₀} (k : E.I₁ i j), IsColimit (P.mapCocone (pres.pres₁ k).cone.op))
    (h : ∀ j, IsLimit <| (pres.preOneHypercover j).multifork (F.op ⋙ P)) :
    IsColimit (P.mapCocone pres.pres.cone.op) := by
  let c := pres.multifork P
  have hc : IsLimit c := by
    refine evaluationJointlyReflectsLimits _ fun j ↦ ?_
    refine IsLimit.ofIsoLimit (h j.unop) (Cone.ext (Iso.refl _) ?_)
    intro l
    simp only [Iso.refl_hom, Functor.mapCone_π_app, c,
      PreOneHypercover.RelativeLimitPresentation.multifork_π_app, NatTrans.op_comp,
      Functor.whiskerRight_comp, evaluation_obj_map, Category.id_comp]
    cases l <;> rfl
  let d := pres.cocone P
  have hd : IsColimit d := pres.isColimit P h₀ h₁
  let natiso : (pres.multicospan P).flip ⋙ colim ≅ d.pt :=
    (colimitIsoFlipCompColim _).symm ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso hd
  let e : Cone d.pt := (Cone.postcompose natiso.hom).obj (colim.mapCone c)
  have he : IsLimit e :=
    (IsLimit.postcomposeHomEquiv natiso _).symm (isLimitOfPreserves _ hc)
  let φ : e.pt ≅ P.obj (op X) := he.conePointUniqueUpToIso hE
  have hφ (k) : φ.hom ≫ (E.multifork P).π.app k = e.π.app k :=
    he.conePointUniqueUpToIso_hom_comp hE k
  have w (j : Jᵒᵖ) (k) : (c.π.app k).app j ≫ (d.ι.app j).app k =
      (P.mapCocone pres.pres.cone.op).ι.app j ≫ (E.multifork P).π.app k := by
    match k with
    | .left k =>
      suffices h : (pres.pres₀ k).π.app (unop j) ≫ F.map ((pres.f k).natTrans.app (unop j)) =
          E.f k ≫ pres.pres.π.app (unop j) by
        simp only [c, d, PreOneHypercover.RelativeLimitPresentation.multifork_π_app,
          Functor.whiskerRight_app, NatTrans.op_app, Functor.comp_map,
          Functor.op_map, Quiver.Hom.unop_op,
          PreOneHypercover.RelativeLimitPresentation.cocone_ι_app_app, ← Functor.map_comp,
          ← op_comp, h, Functor.mapCocone_ι_app, Cone.op_ι, PreOneHypercover.multifork,
          Multifork.ofι_π_app]
      rw [← pres.hf]
      simp
    | .right k =>
      suffices h : (pres.pres₁ k.snd).π.app (unop j) ≫
          F.map ((pres.p₁ k.snd).natTrans.app (unop j) ≫ (pres.f k.fst.1).natTrans.app (unop j)) =
          E.p₁ k.snd ≫ E.f k.fst.1 ≫ pres.pres.π.app (unop j) by
        simp only [c, d, PreOneHypercover.RelativeLimitPresentation.multifork_π_app,
          NatTrans.op_comp, Functor.whiskerRight_comp,
          NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.op_app, Functor.comp_map,
          Functor.op_map, Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp,
          PreOneHypercover.RelativeLimitPresentation.cocone_ι_app_app, h,
          Functor.mapCocone_ι_app, Cone.op_ι, PreOneHypercover.multifork,
          Multifork.ofι_π_app, MulticospanIndex.multicospan_obj_right,
          PreOneHypercover.multicospanIndex_fst]
        simp only [op_comp, Functor.map_comp, Category.assoc]
        rfl
      rw [← pres.hf, ← pres.hp₁]
      simp
  refine IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext φ fun j ↦ ?_)
  refine hE.hom_ext fun k ↦ ?_
  rw [Category.assoc, hφ, ← w]
  simp only [e, natiso, Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
    colim_map, Iso.trans_hom, Iso.symm_hom, colimit.cocone_ι, ι_colimMap_assoc,
    colimitIsoFlipCompColim_inv_app]
  congr 1
  rw [← Category.assoc]
  simp only [HasColimit.ι_isoOfNatIso_inv_assoc, compEvaluation_inv_app]
  erw [Category.id_comp, colimitObjIsoColimitCompEvaluation_ι_inv]
  rw [← NatTrans.comp_app, colimit.comp_coconePointUniqueUpToIso_hom]

end CategoryTheory
