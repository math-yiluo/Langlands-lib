/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ExchangeLeftAdjoint

/-! # Exchange morphisms of the bounded below levelwise derived adjunctions

Let `aj : jS ⊣ jU` and `aj' : jS' ⊣ jU'` be adjunctions of exact functors between abelian
categories, and let `θ : jU ⋙ H ≅ H' ⋙ jU'` for exact functors `H` and `H'`. If the exchange
morphism `exchangeLeft aj aj' θ : H ⋙ jS' ⟶ jS ⋙ H'` is an isomorphism, then so is the exchange
morphism of the bounded below levelwise derived adjunctions `D⁺(jS) ⊣ D⁺(jU)` and
`D⁺(jS') ⊣ D⁺(jU')` with respect to any isomorphism `D⁺(jU) ⋙ D⁺(H) ≅ D⁺(H') ⋙ D⁺(jU')` which
restricts the one induced by `θ` on unbounded derived categories
(`CategoryTheory.Adjunction.isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction`).

The proof embeds everything into the unbounded derived categories along the fully faithful
inclusions `DerivedCategory.Plus.ι`, where the statement is
`CategoryTheory.Adjunction.exchangeLeft_mapDerivedCategoryAdjunction`.

The variant
`CategoryTheory.Adjunction.isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction_of_eqToIso` covers
square isomorphisms passing through a diagonal, as the pullback comparisons of squares of
schemes do.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
  [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D'] [HasDerivedCategory E]

/-- The isomorphism `Functor.mapDerivedCategoryPlusNatIso` is the restriction of
`Functor.mapDerivedCategoryNatIso` along `DerivedCategory.Plus.ι`: the version for inverses of
`Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app`. -/
lemma ι_map_mapDerivedCategoryPlusNatIso_inv_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).inv.app X) =
      (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_epi ((mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Plus.ι.obj X)),
    Iso.hom_inv_id_app, ← ι_map_mapDerivedCategoryPlusNatIso_hom_app, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id]
  rfl

/-- The composition isomorphism `Functor.mapDerivedCategoryPlusCompIso` is the restriction of
`Functor.mapDerivedCategoryCompIso` along `DerivedCategory.Plus.ι`: the version for inverses of
`Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app`. -/
lemma ι_map_mapDerivedCategoryPlusCompIso_inv_app (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).inv.app X) =
      (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_epi ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Plus.ι.obj X)),
    Iso.inv_hom_id_app, ← ι_map_mapDerivedCategoryPlusCompIso_hom_app, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id]
  rfl

/-- Let `e₁ : P ≅ F₁ ⋙ F₂` and `e₂ : Q ≅ G₁ ⋙ G₂` be isomorphisms of exact functors with
`P = Q`. The isomorphism `D⁺(F₁) ⋙ D⁺(F₂) ≅ D⁺(G₁) ⋙ D⁺(G₂)` obtained by composing the
bounded below isomorphisms induced by `e₁` and `e₂` through `D⁺(P) = D⁺(Q)` is the restriction
along `DerivedCategory.Plus.ι` of the isomorphism induced on unbounded derived categories by
`e₁.symm ≪≫ eqToIso h ≪≫ e₂ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂`. -/
lemma ι_map_mapDerivedCategoryPlusCompIso_symm_trans_eqToIso_trans_hom_app
    {F₁ : C ⥤ D} {F₂ : D ⥤ E} {G₁ : C ⥤ D'} {G₂ : D' ⥤ E} {P Q : C ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e₁ : P ≅ F₁ ⋙ F₂) (e₂ : Q ≅ G₁ ⋙ G₂) (h : P = Q)
    (hD : P.mapDerivedCategoryPlus = Q.mapDerivedCategoryPlus) (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        (((mapDerivedCategoryPlusNatIso e₁ ≪≫ mapDerivedCategoryPlusCompIso F₁ F₂).symm ≪≫
          eqToIso hD ≪≫ mapDerivedCategoryPlusNatIso e₂ ≪≫
            mapDerivedCategoryPlusCompIso G₁ G₂).hom.app X) =
      (mapDerivedCategorySquareIso (e₁.symm ≪≫ eqToIso h ≪≫ e₂)).hom.app
        (DerivedCategory.Plus.ι.obj X) := by
  subst h
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp, ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, ι_map_mapDerivedCategoryPlusNatIso_inv_app,
    ι_map_mapDerivedCategoryPlusCompIso_inv_app, mapDerivedCategoryNatIso_trans,
    mapDerivedCategoryNatIso_symm, Category.assoc]

end Functor

namespace Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂] [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {jS : C₁ ⥤ D₁} {jU : D₁ ⥤ C₁} (aj : jS ⊣ jU) {jS' : C₂ ⥤ D₂} {jU' : D₂ ⥤ C₂}
  (aj' : jS' ⊣ jU') {H : C₁ ⥤ C₂} {H' : D₁ ⥤ D₂}
  [jS.Additive] [PreservesFiniteLimits jS] [PreservesFiniteColimits jS]
  [jU.Additive] [PreservesFiniteLimits jU] [PreservesFiniteColimits jU]
  [jS'.Additive] [PreservesFiniteLimits jS'] [PreservesFiniteColimits jS']
  [jU'.Additive] [PreservesFiniteLimits jU'] [PreservesFiniteColimits jU']
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  (θ : jU ⋙ H ≅ H' ⋙ jU')

/-- The unit of the bounded below levelwise derived adjunction
`Adjunction.mapDerivedCategoryPlusAdjunction` is the restriction along
`DerivedCategory.Plus.ι` of the unit of the unbounded one. -/
lemma ι_map_mapDerivedCategoryPlusAdjunction_unit_app (X : DerivedCategory.Plus C₁) :
    DerivedCategory.Plus.ι.map (aj.mapDerivedCategoryPlusAdjunction.unit.app X) =
      aj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusAdjunction, map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The counit of the bounded below levelwise derived adjunction
`Adjunction.mapDerivedCategoryPlusAdjunction` is the restriction along
`DerivedCategory.Plus.ι` of the counit of the unbounded one. -/
lemma ι_map_mapDerivedCategoryPlusAdjunction_counit_app (X : DerivedCategory.Plus D₁) :
    DerivedCategory.Plus.ι.map (aj.mapDerivedCategoryPlusAdjunction.counit.app X) =
      aj.mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusAdjunction, map_restrictFullyFaithful_counit_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- **Exchange morphisms of bounded below levelwise derived adjunctions.** If the exchange
morphism `exchangeLeft aj aj' θ : H ⋙ jS' ⟶ jS ⋙ H'` is an isomorphism, then so is the exchange
morphism `D⁺(H) ⋙ D⁺(jS') ⟶ D⁺(jS) ⋙ D⁺(H')` of any isomorphism
`θp : D⁺(jU) ⋙ D⁺(H) ≅ D⁺(H') ⋙ D⁺(jU')` restricting the isomorphism induced by `θ` on unbounded
derived categories, for the bounded below levelwise derived adjunctions. -/
theorem isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction [IsIso (exchangeLeft aj aj' θ)]
    (θp : jU.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus ≅
      H'.mapDerivedCategoryPlus ⋙ jU'.mapDerivedCategoryPlus)
    (hθ : ∀ X, DerivedCategory.Plus.ι.map (θp.hom.app X) =
      (Functor.mapDerivedCategorySquareIso θ).hom.app (DerivedCategory.Plus.ι.obj X)) :
    IsIso (exchangeLeft aj.mapDerivedCategoryPlusAdjunction aj'.mapDerivedCategoryPlusAdjunction
      θp) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι]
  have e₁ : DerivedCategory.Plus.ι.map (jS'.mapDerivedCategoryPlus.map
      (H.mapDerivedCategoryPlus.map (aj.mapDerivedCategoryPlusAdjunction.unit.app X))) =
      jS'.mapDerivedCategory.map (H.mapDerivedCategory.map
        (aj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Plus.ι.obj X))) := by
    rw [← ι_map_mapDerivedCategoryPlusAdjunction_unit_app]
    rfl
  have e₂ : DerivedCategory.Plus.ι.map (jS'.mapDerivedCategoryPlus.map
      (θp.hom.app (jS.mapDerivedCategoryPlus.obj X))) =
      jS'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso θ).hom.app
        (jS.mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj X))) :=
    congrArg jS'.mapDerivedCategory.map (hθ (jS.mapDerivedCategoryPlus.obj X))
  have h : DerivedCategory.Plus.ι.map ((exchangeLeft aj.mapDerivedCategoryPlusAdjunction
      aj'.mapDerivedCategoryPlusAdjunction θp).app X) =
      (exchangeLeft aj.mapDerivedCategoryAdjunction aj'.mapDerivedCategoryAdjunction
        (Functor.mapDerivedCategorySquareIso θ)).app (DerivedCategory.Plus.ι.obj X) := by
    rw [exchangeLeft_app, exchangeLeft_app, Functor.map_comp, Functor.map_comp, e₁, e₂,
      ι_map_mapDerivedCategoryPlusAdjunction_counit_app]
    rfl
  rw [h, exchangeLeft_mapDerivedCategoryAdjunction]
  infer_instance

/-- The form of `Adjunction.isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction` for a square
isomorphism `e₁.symm ≪≫ eqToIso h ≪≫ e₂ : jU ⋙ H ≅ H' ⋙ jU'` passing through a diagonal
`P = Q`, with its bounded below counterpart assembled from the isomorphisms induced by `e₁` and
`e₂` on bounded below derived categories. -/
theorem isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction_of_eqToIso {P Q : D₁ ⥤ C₂}
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e₁ : P ≅ jU ⋙ H) (e₂ : Q ≅ H' ⋙ jU') (h : P = Q)
    (hD : P.mapDerivedCategoryPlus = Q.mapDerivedCategoryPlus)
    [IsIso (exchangeLeft aj aj' (e₁.symm ≪≫ eqToIso h ≪≫ e₂))] :
    IsIso (exchangeLeft aj.mapDerivedCategoryPlusAdjunction aj'.mapDerivedCategoryPlusAdjunction
      ((Functor.mapDerivedCategoryPlusNatIso e₁ ≪≫
          Functor.mapDerivedCategoryPlusCompIso jU H).symm ≪≫
        eqToIso hD ≪≫ Functor.mapDerivedCategoryPlusNatIso e₂ ≪≫
          Functor.mapDerivedCategoryPlusCompIso H' jU')) :=
  isIso_exchangeLeft_mapDerivedCategoryPlusAdjunction aj aj' _ _
    (Functor.ι_map_mapDerivedCategoryPlusCompIso_symm_trans_eqToIso_trans_hom_app e₁ e₂ h hD)

end Adjunction

end CategoryTheory
