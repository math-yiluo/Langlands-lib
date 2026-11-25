/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyComp

/-!
# Homology of the derived exchange morphism of exact adjoint pairs

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions of exact functors between abelian
categories, `u` and `v` exact functors and `β : u ⋙ f₂ ≅ f₁ ⋙ v`, with exchange morphism
`exchangeRight adj₁ adj₂ β : g₁ ⋙ u ⟶ v ⋙ g₂` (for instance the base-change morphism of a
commutative square of schemes on sheaves). If this exchange morphism is an isomorphism, then:

- the exchange morphism of the induced isomorphism `D(u) ⋙ D(f₂) ≅ D(f₁) ⋙ D(v)` for the
  levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)` is the isomorphism induced
  by the exchange morphism (`CategoryTheory.Adjunction.exchangeRight_mapDerivedCategoryAdjunction`);
- on homology, it is the exchange morphism of `β`
  (`CategoryTheory.Adjunction.homologyFunctor_map_exchangeRight_mapDerivedCategoryAdjunction`);
- the same holds for the exchange morphism of the total derived adjunctions `Lf₁ ⊣ Rg₁` and
  `Lf₂ ⊣ Rg₂` with respect to an isomorphism `θ : Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` corresponding to `β`
  (`CategoryTheory.Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`): under
  homology, the derived base-change morphism is the underived one.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

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
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (β : u ⋙ f₂ ≅ f₁ ⋙ v)

/-- **The levelwise derived exchange morphism**: if the exchange morphism of `β` is an
isomorphism, the exchange morphism of the induced isomorphism `D(u) ⋙ D(f₂) ≅ D(f₁) ⋙ D(v)`
for the levelwise derived adjunctions is the isomorphism induced by the exchange morphism of
`β`. This is `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate`, together with the
characterization of exchange morphisms by their compatibility with the units. -/
lemma exchangeRight_mapDerivedCategoryAdjunction [IsIso (exchangeRight adj₁ adj₂ β)] :
    exchangeRight adj₁.mapDerivedCategoryAdjunction adj₂.mapDerivedCategoryAdjunction
        (Functor.mapDerivedCategorySquareIso β) =
      (Functor.mapDerivedCategorySquareIso (asIso (exchangeRight adj₁ adj₂ β))).hom :=
  exchangeRight_eq_of_map_unit_app_comp _ _ _ _ fun M ↦
    (mapDerivedCategoryAdjunction_mate adj₁ adj₂ (asIso (exchangeRight adj₁ adj₂ β)) β
      (fun K ↦ (map_unit_comp_exchangeRight_app adj₁ adj₂ β K).symm) M).symm

/-- **Homology of the levelwise derived exchange morphism**: if the exchange morphism of `β` is
an isomorphism, then on the homology objects, the exchange morphism of the levelwise derived
adjunctions is the exchange morphism of `β`, through the commutations of the exact functors with
homology. -/
@[reassoc]
lemma homologyFunctor_map_exchangeRight_mapDerivedCategoryAdjunction
    [IsIso (exchangeRight adj₁ adj₂ β)] (n : ℤ) (K : DerivedCategory D₁) :
    u.map ((g₁.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (u.mapDerivedCategoryHomologyFunctorIso n).hom.app (g₁.mapDerivedCategory.obj K) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          ((exchangeRight adj₁.mapDerivedCategoryAdjunction adj₂.mapDerivedCategoryAdjunction
            (Functor.mapDerivedCategorySquareIso β)).app K) =
      (exchangeRight adj₁ adj₂ β).app ((DerivedCategory.homologyFunctor D₁ n).obj K) ≫
        g₂.map ((v.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (g₂.mapDerivedCategoryHomologyFunctorIso n).hom.app (v.mapDerivedCategory.obj K) := by
  rw [exchangeRight_mapDerivedCategoryAdjunction]
  exact Functor.mapDerivedCategoryHomologyFunctorIso_squareIso
    (asIso (exchangeRight adj₁ adj₂ β)) n K

section Derived

variable [MonoidalCategory D₁] [MonoidalPreadditive D₁] [HasCountableCoproducts D₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D₁] [HasExactColimitsOfShape ℤ D₁]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).obj X)]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D₁]
  (θ : u.leftDerivedFunctor ⋙ f₂.leftDerivedFunctor ≅ f₁.leftDerivedFunctor ⋙ v.leftDerivedFunctor)

/-- **Homology of the derived exchange morphism**: let `θ : Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` correspond to
`β : u ⋙ f₂ ≅ f₁ ⋙ v` through the identifications of the total left derived functors of the
exact functors with the levelwise ones (`hθ`). If the exchange morphism of `β` is an isomorphism,
then on the homology objects, the exchange morphism of `θ` for the derived adjunctions
`Lf₁ ⊣ Rg₁` and `Lf₂ ⊣ Rg₂` is the exchange morphism of `β`, through the commutations of the
total derived functors with homology. -/
lemma homologyFunctor_map_exchangeRight_derivedAdjunction [IsIso (exchangeRight adj₁ adj₂ β)]
    (hθ : ∀ K, f₂.mapDerivedCategory.map (u.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
      f₂.leftDerivedFunctorIsoMapDerivedCategory.inv.app (u.leftDerivedFunctor.obj K) ≫
        θ.hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app K ≫
        v.mapDerivedCategory.map (f₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        v.leftDerivedFunctorIsoMapDerivedCategory.inv.app (f₁.leftDerivedFunctor.obj K))
    (n : ℤ) (K : DerivedCategory D₁) :
    u.map ((g₁.rightDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (u.leftDerivedFunctorHomologyFunctorIso n).hom.app (g₁.rightDerivedFunctor.obj K) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          ((exchangeRight adj₁.derivedAdjunction adj₂.derivedAdjunction θ).app K) =
      (exchangeRight adj₁ adj₂ β).app ((DerivedCategory.homologyFunctor D₁ n).obj K) ≫
        g₂.map ((v.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (g₂.rightDerivedFunctorHomologyFunctorIso n).hom.app (v.leftDerivedFunctor.obj K) := by
  have hA := map_exchangeRight_app_of_comm adj₁.derivedAdjunction adj₂.derivedAdjunction θ
    adj₁.mapDerivedCategoryAdjunction adj₂.mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategorySquareIso β)
    (HB := 𝟭 _) (HA := 𝟭 _) (HB' := 𝟭 _) (HA' := 𝟭 _)
    (Functor.leftUnitor _ ≪≫ f₁.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ g₁.rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ f₂.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ g₂.rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ u.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ v.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.rightUnitor _).symm)
    (fun K ↦ by simp [mapDerivedCategoryAdjunction])
    (fun K ↦ by simp [mapDerivedCategoryAdjunction])
    (fun K ↦ by simpa using hθ K) K
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id] at hA
  have hA' := (DerivedCategory.homologyFunctor C₂ n).congr_map hA
  have e₁ := (u.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
    (g₁.rightDerivedFunctorIsoMapDerivedCategory.inv.app K)
  have e₃ := (g₂.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
    (v.leftDerivedFunctorIsoMapDerivedCategory.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hA' e₁ e₃
  simp only [Functor.rightDerivedFunctorHomologyFunctorIso,
    Functor.leftDerivedFunctorHomologyFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% e₁, hA', homologyFunctor_map_exchangeRight_mapDerivedCategoryAdjunction_assoc,
    reassoc_of% e₃]

/-- The isomorphism `Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` of total left derived functors induced by
`β : u ⋙ f₂ ≅ f₁ ⋙ v`, through the composition isomorphisms of total left derived functors of exact
functors. -/
noncomputable def leftDerivedFunctorSquareIso :
    u.leftDerivedFunctor ⋙ f₂.leftDerivedFunctor ≅ f₁.leftDerivedFunctor ⋙ v.leftDerivedFunctor :=
  (u.leftDerivedFunctorCompIso f₂).symm ≪≫ (u ⋙ f₂).leftDerivedFunctorNatIso β ≪≫
    f₁.leftDerivedFunctorCompIso v

omit [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂] in
/-- The isomorphism `leftDerivedFunctorSquareIso β` corresponds to the isomorphism
`D(u) ⋙ D(f₂) ≅ D(f₁) ⋙ D(v)` induced by `β`, through the identifications of the total left
derived functors of the exact functors with the levelwise ones. -/
lemma leftDerivedFunctorSquareIso_hom_app (K : DerivedCategory C₁) :
    f₂.mapDerivedCategory.map (u.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
      f₂.leftDerivedFunctorIsoMapDerivedCategory.inv.app (u.leftDerivedFunctor.obj K) ≫
        (leftDerivedFunctorSquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app K ≫
        v.mapDerivedCategory.map (f₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        v.leftDerivedFunctorIsoMapDerivedCategory.inv.app (f₁.leftDerivedFunctor.obj K) := by
  simp [leftDerivedFunctorSquareIso, Functor.leftDerivedFunctorCompIso,
    Functor.leftDerivedFunctorNatIso]

omit [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂] in
/-- The isomorphism `leftDerivedFunctorSquareIso β` for `β` the composite
`u ⋙ f₂ ≅ P = Q ≅ f₁ ⋙ v` of isomorphisms of exact functors: it is the composite of the derived
isomorphisms. -/
lemma leftDerivedFunctorSquareIso_hom_app_of_eq {P Q : C₁ ⥤ D₂} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] [Q.Additive] [PreservesFiniteLimits Q]
    [PreservesFiniteColimits Q] (cP : P ≅ u ⋙ f₂) (cQ : Q ≅ f₁ ⋙ v) (h : P = Q)
    (hβ : β = cP.symm ≪≫ eqToIso h ≪≫ cQ) (K : DerivedCategory C₁) :
    (leftDerivedFunctorSquareIso β).hom.app K =
      (u.leftDerivedFunctorCompIso f₂).inv.app K ≫ (P.leftDerivedFunctorNatIso cP).inv.app K ≫
        eqToHom (by subst h; rfl) ≫ (Q.leftDerivedFunctorNatIso cQ).hom.app K ≫
        (f₁.leftDerivedFunctorCompIso v).hom.app K := by
  subst hβ h
  simp [leftDerivedFunctorSquareIso, Functor.leftDerivedFunctorNatIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]

/-- **Homology of the derived exchange morphism**, for the isomorphism
`leftDerivedFunctorSquareIso β : Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` induced by `β`: if the exchange morphism of
`β` is an isomorphism, then on the homology objects, the exchange morphism for the derived
adjunctions `Lf₁ ⊣ Rg₁` and `Lf₂ ⊣ Rg₂` is the exchange morphism of `β`. -/
lemma homologyFunctor_map_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso
    [IsIso (exchangeRight adj₁ adj₂ β)] (n : ℤ) (K : DerivedCategory D₁) :
    u.map ((g₁.rightDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (u.leftDerivedFunctorHomologyFunctorIso n).hom.app (g₁.rightDerivedFunctor.obj K) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          ((exchangeRight adj₁.derivedAdjunction adj₂.derivedAdjunction
            (leftDerivedFunctorSquareIso β)).app K) =
      (exchangeRight adj₁ adj₂ β).app ((DerivedCategory.homologyFunctor D₁ n).obj K) ≫
        g₂.map ((v.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (g₂.rightDerivedFunctorHomologyFunctorIso n).hom.app (v.leftDerivedFunctor.obj K) :=
  homologyFunctor_map_exchangeRight_derivedAdjunction adj₁ adj₂ β _
    (leftDerivedFunctorSquareIso_hom_app β) n K

end Derived

end CategoryTheory.Adjunction
