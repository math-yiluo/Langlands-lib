/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractDescent
public import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityDerivedFactors

/-! # Generic unit equation of a normalized derived square

The unit equation of a derived square normalized on representatives, stated over variables for
every category, instance, functor and comparison, with their defining equations as hypotheses.
Instantiating it at a goal with the goal's own instance terms avoids kernel conversions between
different instance paths.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.FdIntegralScalarForward

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u₅

/-- Natural transformations agreeing on the image of an essentially surjective functor agree. -/
theorem app_eq_of_essSurj' {C : Type u₁} {D : Type u₂} {A : Type u₃} [Category.{v₁} C]
    [Category.{v₂} D] [Category.{v₃} A] (Q : C ⥤ D) [Q.EssSurj] {F G : D ⥤ A}
    (α β : F ⟶ G) (h : ∀ P, α.app (Q.obj P) = β.app (Q.obj P)) (Y : D) :
    α.app Y = β.app Y := by
  let i := Q.objObjPreimageIso Y
  have hα := α.naturality i.hom
  have hβ := β.naturality i.hom
  rw [h] at hα
  rw [← cancel_epi (F.map i.hom), hα, hβ]

/-- The unit equation of a normalized derived square, from its chain-level counterpart. -/
theorem unit_full {KE : Type u₁} {PE : Type u₂} {DE : Type u₃} {EE : Type u₄}
    [Category.{v₁} KE] [Category.{v₂} PE] [Category.{v₃} DE] [Category.{v₄} EE]
    (QE : KE ⥤ DE) [QE.EssSurj] (RE : PE ⥤ EE) (oh : KE ⥤ KE) (tE : KE ⥤ PE) (xh : PE ⥤ PE)
    (Oh : DE ⥤ DE) (TE : DE ⥤ EE) (Xh : EE ⥤ EE)
    (foh : QE ⋙ Oh ≅ oh ⋙ QE) (ftE : QE ⋙ TE ≅ tE ⋙ RE) (εh : RE ⋙ Xh ⟶ xh ⋙ RE)
    (ch : oh ⋙ tE ≅ tE ⋙ xh) (ou : oh ≅ 𝟭 KE) (xu : xh ≅ 𝟭 PE)
    (eh : Oh ⋙ TE ≅ TE ⋙ Xh) (Ou : Oh ≅ 𝟭 DE) (Xu : Xh ≅ 𝟭 EE)
    (heh : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) =
      TE.map (foh.hom.app P) ≫ ftE.hom.app (oh.obj P) ≫ RE.map (ch.hom.app P))
    (hOu : ∀ P, Ou.hom.app (QE.obj P) = foh.hom.app P ≫ QE.map (ou.hom.app P))
    (hXu : ∀ P, Xu.hom.app (RE.obj P) = εh.app P ≫ RE.map (xu.hom.app P))
    (hc : ∀ P, tE.map (ou.hom.app P) = ch.hom.app P ≫ xu.hom.app (tE.obj P))
    (Y : DE) :
    eh.inv.app Y ≫ TE.map (Ou.hom.app Y) = Xu.hom.app (TE.obj Y) := by
  let α : TE ⋙ Xh ⟶ TE :=
    eh.inv ≫ Functor.whiskerRight Ou.hom TE ≫ (Functor.leftUnitor TE).hom
  let β : TE ⋙ Xh ⟶ TE := Functor.whiskerLeft TE Xu.hom ≫ (Functor.rightUnitor TE).hom
  have := app_eq_of_essSurj' QE α β (fun P ↦ by
    simpa [α, β] using derived_unit QE RE oh tE xh Oh TE Xh foh ftE εh ch ou xu eh Ou Xu heh
      hOu hXu (fun P ↦ by rw [hc P, Iso.inv_hom_id_app_assoc]) P) Y
  simpa [α, β] using this

/-- The unit equation of the normalized derived square of an exact functor family at an index
equal to the identity index, with every functor and instance given as a variable. -/
theorem unit_generic {C : Type u₁} [Category.{v₁} C] [aC : Abelian C] [dC : HasDerivedCategory C]
    {K : Type u₂} (F : K → C ⥤ C) [hFa : ∀ k, (F k).Additive]
    [hFl : ∀ k, PreservesFiniteLimits (F k)] [hFc : ∀ k, PreservesFiniteColimits (F k)]
    (k k₀ : K) (hk : k = k₀) (a : F k₀ ≅ 𝟭 C)
    (Oh Oh' : DerivedCategory C ⥤ DerivedCategory C) (hOh : Oh = (F k).mapDerivedCategory)
    (hOh' : Oh' = (F k₀).mapDerivedCategory) (U : Oh' ≅ 𝟭 (DerivedCategory C))
    (hU : U ≍ Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso C)
    (oh : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (hoh : oh = (F k).mapHomologicalComplex (.up ℤ))
    (foh : DerivedCategory.Q ⋙ Oh ≅ oh ⋙ DerivedCategory.Q)
    (hfoh : foh ≍ (F k).mapDerivedCategoryFactors) (ou : oh ≅ 𝟭 (CochainComplex C ℤ))
    (hou : ou ≍ NatIso.mapHomologicalComplex (eqToIso (congrArg F hk) ≪≫ a) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso C (.up ℤ))
    {PE : Type u₃} {EE : Type u₄} [Category.{v₃} PE] [Category.{v₄} EE]
    (RE : PE ⥤ EE) (tE : CochainComplex C ℤ ⥤ PE) (xh : PE ⥤ PE)
    (TE : DerivedCategory C ⥤ EE) (Xh : EE ⥤ EE)
    (ftE : DerivedCategory.Q ⋙ TE ≅ tE ⋙ RE) (εh : RE ⋙ Xh ⟶ xh ⋙ RE)
    (ch : oh ⋙ tE ≅ tE ⋙ xh) (xu : xh ≅ 𝟭 PE)
    (eh : Oh ⋙ TE ≅ TE ⋙ Xh) (Xu : Xh ≅ 𝟭 EE)
    (heh : ∀ P, eh.hom.app (DerivedCategory.Q.obj P) ≫ Xh.map (ftE.hom.app P) ≫
        εh.app (tE.obj P) =
      TE.map (foh.hom.app P) ≫ ftE.hom.app (oh.obj P) ≫ RE.map (ch.hom.app P))
    (hXu : ∀ P, Xu.hom.app (RE.obj P) = εh.app P ≫ RE.map (xu.hom.app P))
    (hc : ∀ P, tE.map (ou.hom.app P) = ch.hom.app P ≫ xu.hom.app (tE.obj P))
    (e : Oh = Oh') (Y : DerivedCategory C) :
    eh.inv.app Y ≫ TE.map (eqToHom (Functor.congr_obj e Y) ≫ U.hom.app Y) =
      Xu.hom.app (TE.obj Y) := by
  subst hOh hOh' hoh hk
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hfoh
  obtain rfl := eq_of_heq hou
  have h := unit_full DerivedCategory.Q RE _ tE xh _ TE Xh _ ftE εh ch _ xu eh
    (eqToIso e ≪≫ (Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso C))
    Xu heh (fun P ↦ ?_) hXu hc Y
  · simpa [eqToHom_app] using h
  · simp only [eqToIso_refl, Iso.refl_trans]
    exact podIdentityDerivedFactors _ _ P

end WeilConjectures.FdIntegralScalarForward
