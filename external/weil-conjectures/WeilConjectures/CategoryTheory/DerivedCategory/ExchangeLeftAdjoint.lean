/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived exchange morphisms from exact left adjoints of the base change functors

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions between abelian categories with exact
left adjoints `f₁`, `f₂`, and let `β : u ⋙ f₂ ≅ f₁ ⋙ v` for exact functors `u` and `v`. If `u`
and `v` have exact left adjoints `ul ⊣ u` and `vl ⊣ v` (for instance when `u` and `v` are
pullbacks along étale morphisms, with left adjoints the extensions by zero), and the exchange
morphism `exchangeRight adj₁ adj₂ β : g₁ ⋙ u ⟶ v ⋙ g₂` is an isomorphism, then so is the exchange
morphism of the derived adjunctions `Lf₁ ⊣ Rg₁` and `Lf₂ ⊣ Rg₂`
(`CategoryTheory.Adjunction.isIso_exchangeRight_derivedAdjunction_of_leftAdjoint`), without any
exactness assumption on `g₁` and `g₂`.

The proof goes through the exchange morphism `exchangeLeft au av β : f₂ ⋙ vl ⟶ ul ⋙ f₁`, which is
conjugate to `exchangeRight adj₁ adj₂ β`
(`CategoryTheory.Adjunction.isIso_exchangeRight_iff_isIso_exchangeLeft`). Since all the functors
in it are exact, it is computed levelwise on derived categories
(`CategoryTheory.Adjunction.exchangeLeft_mapDerivedCategoryAdjunction`), and conjugating back at
the derived level gives the result.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

section Levelwise

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

/-- **The levelwise derived exchange morphism along right adjoints**: if the exchange morphism
`exchangeLeft aj aj' θ : H ⋙ jS' ⟶ jS ⋙ H'` is an isomorphism, the exchange morphism of the
induced isomorphism `D(jU) ⋙ D(H) ≅ D(H') ⋙ D(jU')` for the levelwise derived adjunctions is the
isomorphism induced by `exchangeLeft aj aj' θ`. -/
lemma exchangeLeft_mapDerivedCategoryAdjunction [IsIso (exchangeLeft aj aj' θ)] :
    exchangeLeft aj.mapDerivedCategoryAdjunction aj'.mapDerivedCategoryAdjunction
        (Functor.mapDerivedCategorySquareIso θ) =
      (Functor.mapDerivedCategorySquareIso (asIso (exchangeLeft aj aj' θ))).hom :=
  exchangeLeft_eq_of_unit_app_comp _ _ _ _ <|
    mapDerivedCategoryAdjunction_mate aj aj' θ (asIso (exchangeLeft aj aj' θ))
      (unit_app_comp_map_exchangeLeft_app aj aj' θ)

/-- If the exchange morphism `exchangeLeft aj aj' θ` is an isomorphism, so is the exchange
morphism of the induced isomorphism `D(jU) ⋙ D(H) ≅ D(H') ⋙ D(jU')` for the levelwise derived
adjunctions. -/
instance isIso_exchangeLeft_mapDerivedCategoryAdjunction [IsIso (exchangeLeft aj aj' θ)] :
    IsIso (exchangeLeft aj.mapDerivedCategoryAdjunction aj'.mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategorySquareIso θ)) := by
  rw [exchangeLeft_mapDerivedCategoryAdjunction]
  infer_instance

end Levelwise

section Derived

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
  [MonoidalCategory D₁] [MonoidalPreadditive D₁] [HasCountableCoproducts D₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D₁] [HasExactColimitsOfShape ℤ D₁]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).obj X)]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D₁]
  [MonoidalCategory D₂] [MonoidalPreadditive D₂] [HasCountableCoproducts D₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D₂] [HasExactColimitsOfShape ℤ D₂]
  [∀ (X : D₂), PreservesColimitsOfShape ℤ ((curriedTensor D₂).obj X)]
  [∀ (X : D₂), PreservesColimitsOfShape ℤ ((curriedTensor D₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂] [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions D₁]
  [HasKInjectiveResolutions D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂} {ul : C₂ ⥤ C₁} {vl : D₂ ⥤ D₁}
  (au : ul ⊣ u) (av : vl ⊣ v)
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁] [g₁.Additive]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂] [g₂.Additive]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  [ul.Additive] [PreservesFiniteLimits ul] [PreservesFiniteColimits ul]
  [vl.Additive] [PreservesFiniteLimits vl] [PreservesFiniteColimits vl]
  (β : u ⋙ f₂ ≅ f₁ ⋙ v)
  (θ : u.leftDerivedFunctor ⋙ f₂.leftDerivedFunctor ≅ f₁.leftDerivedFunctor ⋙ v.leftDerivedFunctor)

include au av in
/-- **Derived base change from exact left adjoints of the base change functors.** Let
`θ : Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` correspond to `β : u ⋙ f₂ ≅ f₁ ⋙ v` through the identifications of
the total left derived functors of the exact functors with the levelwise ones (`hθ`). If `u` and
`v` have exact left adjoints and the exchange morphism of `β` is an isomorphism, then the exchange
morphism of `θ` for the derived adjunctions `Lf₁ ⊣ Rg₁` and `Lf₂ ⊣ Rg₂` is an isomorphism. -/
theorem isIso_exchangeRight_derivedAdjunction_of_leftAdjoint
    [IsIso (exchangeRight adj₁ adj₂ β)]
    (hθ : ∀ K, f₂.mapDerivedCategory.map (u.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
      f₂.leftDerivedFunctorIsoMapDerivedCategory.inv.app (u.leftDerivedFunctor.obj K) ≫
        θ.hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app K ≫
        v.mapDerivedCategory.map (f₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        v.leftDerivedFunctorIsoMapDerivedCategory.inv.app (f₁.leftDerivedFunctor.obj K)) :
    IsIso (exchangeRight adj₁.derivedAdjunction adj₂.derivedAdjunction θ) := by
  -- The exchange morphism of `β` along the left adjoints of `u` and `v` is an isomorphism.
  have : IsIso (exchangeLeft au av β) :=
    (isIso_exchangeRight_iff_isIso_exchangeLeft adj₁ adj₂ au av β).1 inferInstance
  -- The derived adjunctions, with the levelwise left adjoints.
  let A₁ := adj₁.derivedAdjunction.ofNatIsoLeft f₁.leftDerivedFunctorIsoMapDerivedCategory
  let A₂ := adj₂.derivedAdjunction.ofNatIsoLeft f₂.leftDerivedFunctorIsoMapDerivedCategory
  have hA : IsIso (exchangeRight A₁ A₂ (Functor.mapDerivedCategorySquareIso β)) :=
    (isIso_exchangeRight_iff_isIso_exchangeLeft A₁ A₂ au.mapDerivedCategoryAdjunction
      av.mapDerivedCategoryAdjunction _).2 inferInstance
  rw [NatTrans.isIso_iff_isIso_app] at hA ⊢
  intro K
  have h := map_exchangeRight_app_of_comm adj₁.derivedAdjunction adj₂.derivedAdjunction θ
    A₁ A₂ (Functor.mapDerivedCategorySquareIso β)
    (HB := 𝟭 _) (HA := 𝟭 _) (HB' := 𝟭 _) (HA' := 𝟭 _)
    (Functor.leftUnitor _ ≪≫ f₁.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ f₂.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ u.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ v.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (fun K ↦ by simp [A₂]) (fun K ↦ by simp [A₁]) (fun K ↦ by simpa using hθ K) K
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_id] at h
  have e : (exchangeRight adj₁.derivedAdjunction adj₂.derivedAdjunction θ).app K =
      u.leftDerivedFunctorIsoMapDerivedCategory.hom.app (g₁.rightDerivedFunctor.obj K) ≫
        (exchangeRight A₁ A₂ (Functor.mapDerivedCategorySquareIso β)).app K ≫
        g₂.rightDerivedFunctor.map (v.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) := by
    rw [← h, Iso.hom_inv_id_app_assoc]
  have := hA K
  rw [e]
  infer_instance

include au av in
/-- **Derived base change from exact left adjoints of the base change functors**, for the
isomorphism `leftDerivedFunctorSquareIso β : Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` induced by `β`: if `u` and `v`
have exact left adjoints and the exchange morphism of `β` is an isomorphism, then so is the
exchange morphism for the derived adjunctions `Lf₁ ⊣ Rg₁` and `Lf₂ ⊣ Rg₂`. -/
theorem isIso_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso_of_leftAdjoint
    [IsIso (exchangeRight adj₁ adj₂ β)] :
    IsIso (exchangeRight adj₁.derivedAdjunction adj₂.derivedAdjunction
      (leftDerivedFunctorSquareIso β)) :=
  isIso_exchangeRight_derivedAdjunction_of_leftAdjoint adj₁ adj₂ au av β _
    (leftDerivedFunctorSquareIso_hom_app β)

end Derived

end CategoryTheory.Adjunction
