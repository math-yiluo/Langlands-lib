/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Grothendieck module sheaves in an independent coefficient universe

Source: Stacks 03DA, 03DB and 079Q.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

/-- Module sheaves are Grothendieck abelian whenever the site is essentially small in
the coefficient universe. Source: Stacks 03DA, 03DB and 079Q
(auxiliary; not a blueprint node).
Proof: restrict underlying presheaves to a small model of the site to obtain small Hom
sets. Free sheaves on the shrink-Yoneda presheaves of the chosen representative objects
form a small separating family: the free/sheafification adjunction identifies a map
from one of these sheaves with a section, and sections distinguish morphisms on the
small model. Their coproduct is a separator. Filtered colimits are exact because the
faithful exact forgetful functor to abelian sheaves preserves and reflects colimits.
No inequality between the raw site universes and the coefficient universe is needed. -/
theorem isGrothendieckAbelian_coefficientUniverse
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (S : Sheaf J RingCat.{w}) : IsGrothendieckAbelian.{w} (SheafOfModules.{w} S) := by
  classical
  let e := equivSmallModel.{w} C
  let B := SheafOfModules.{w} S
  let F := PresheafOfModules.toPresheaf.{w} S.obj ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj e.inverse.op
  have : LocallySmall.{w} (PresheafOfModules.{w} S.obj) := locallySmall_of_faithful F
  have : LocallySmall.{w} B := locallySmall_of_faithful (SheafOfModules.forget S)
  have hsep : ObjectProperty.IsSeparating (.ofObj fun U : SmallModel.{w} C ↦
      (PresheafOfModules.sheafification.{w} (𝟙 S.obj)).obj
        ((PresheafOfModules.free S.obj).obj (shrinkYoneda.{w}.obj (e.inverse.obj U)))) := by
    let adj := (PresheafOfModules.freeAdjunction S.obj).comp
      (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 S.obj))
    intro M N f g h
    let G := SheafOfModules.forget S ⋙ F ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{w})
    apply G.map_injective
    ext V x
    let a : shrinkYoneda.{w}.obj (e.inverse.obj V.unop) ⟶
        M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w} :=
      shrinkYonedaEquiv.symm x
    have heq := h _ (ObjectProperty.ofObj_apply _ V.unop) ((adj.homEquiv _ _).symm a)
    have hh := congrArg (adj.homEquiv _ _) heq
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right] at hh
    erw [Equiv.apply_symm_apply] at hh
    have hx := congrArg shrinkYonedaEquiv hh
    dsimp only [a] at hx
    erw [shrinkYonedaEquiv_comp, shrinkYonedaEquiv_comp] at hx
    erw [Equiv.apply_symm_apply] at hx
    change f.val.app (op (e.inverse.obj V.unop)) x =
      g.val.app (op (e.inverse.obj V.unop)) x at hx ⊢
    exact hx
  have : HasFilteredColimitsOfSize.{w, w} B := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{w, w} B :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf.{w} S)⟩
  have : HasColimitsOfShape (Discrete (SmallModel.{w} C)) (PresheafOfModules.{w} S.obj) :=
    PresheafOfModules.hasColimitsOfShape S.obj _
  have : HasColimitsOfShape (Discrete (SmallModel.{w} C)) B :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf S _
  have : HasSeparator B := ⟨_, hsep.isSeparator_coproduct⟩
  exact {}

end SheafOfModules
