/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.NatIso
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Trivializations of left derived functors

Let `F : C ⥤ C` be an exact endofunctor of an abelian category with functorial flat
resolutions, and `e : F ≅ 𝟭 C` a trivialization of `F`. Then the total left derived functor
of `F` is trivialized as well, `L(F) ≅ L(𝟭) ≅ D(𝟭) ≅ 𝟭`
(`CategoryTheory.Functor.leftDerivedFunctorIdIso`). We show that this construction is
compatible with composition and with commutative squares of exact functors; both statements
are checked on the image of the homotopy category, through the counits of the derived
functors (`CategoryTheory.Functor.leftDerivedFunctorIdIso_hom_app_Qh_obj`).

## Main statements

- `CategoryTheory.Functor.leftDerivedFunctorIdIso_comp`: compatibility with composition.
- `CategoryTheory.Functor.leftDerivedFunctorIdIso_square`: compatibility with a commutative
  square.
-/

@[expose] public section

universe wC wD vC vD uC uD

open CategoryTheory Limits

namespace CategoryTheory.Functor

open MonoidalCategory DerivedCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]

/-- The composite `e.hom ≫ (𝟭 ≅ 𝟭)` on the image of a complex in the homotopy category. -/
lemma mapHomotopyCategory_isoId_quotient_obj {F : C ⥤ D} {G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ⟶ G) (K : CochainComplex C ℤ) :
    (NatTrans.mapHomotopyCategory e (.up ℤ)).app ((HomotopyCategory.quotient C _).obj K) =
      (HomotopyCategory.quotient D _).map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K) :=
  rfl

/-- The homotopy category statement behind `leftDerivedFunctorIdIso_comp`. -/
lemma mapHomotopyCategory_isoId_comp {F G H : C ⥤ C} [F.Additive] [G.Additive] [H.Additive]
    (eF : F ≅ 𝟭 C) (eG : G ≅ 𝟭 C) (c : H ≅ F ⋙ G)
    (P : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P ≫
        ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app
            ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app
            ((F.mapHomotopyCategory (.up ℤ)).obj P)) ≫
        (NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P =
      (NatTrans.mapHomotopyCategory (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG).hom
          (.up ℤ)).app P ≫
        (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  erw [mapHomotopyCategoryIdIso_hom_app, mapHomotopyCategoryIdIso_hom_app]
  rw [mapHomotopyCategory_isoId_quotient_obj, mapHomotopyCategory_isoId_quotient_obj,
    mapHomotopyCategory_isoId_quotient_obj]
  erw [mapHomotopyCategory_isoId_quotient_obj]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexIdIso_hom_app_f, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, leftUnitor_hom_app,
    Category.id_comp, id_obj, comp_obj]
  erw [Category.comp_id, Category.comp_id]
  rw [eG.hom.naturality]
  erw [Category.comp_id]
  rfl

/-- The homotopy category statement behind `leftDerivedFunctorIdIso_square`. -/
lemma mapHomotopyCategory_isoId_square {F : C ⥤ C} {G : C ⥤ D} {F' : D ⥤ D} [F.Additive]
    [G.Additive] [F'.Additive] (eF : F ≅ 𝟭 C) (eF' : F' ≅ 𝟭 D) (c : F ⋙ G ≅ G ⋙ F')
    (hc : c.hom ≫ whiskerLeft G eF'.hom = whiskerRight eF.hom G ≫ G.leftUnitor.hom ≫
      G.rightUnitor.inv) (P : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P ≫
        (NatTrans.mapHomotopyCategory eF'.hom (.up ℤ)).app
            ((G.mapHomotopyCategory (.up ℤ)).obj P) ≫
          (mapHomotopyCategoryIdIso D (.up ℤ)).hom.app ((G.mapHomotopyCategory (.up ℤ)).obj P) =
      (G.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  erw [mapHomotopyCategoryIdIso_hom_app, mapHomotopyCategoryIdIso_hom_app]
  rw [mapHomotopyCategory_isoId_quotient_obj, mapHomotopyCategory_isoId_quotient_obj]
  erw [mapHomotopyCategory_isoId_quotient_obj]
  rw [← (HomotopyCategory.quotient C (.up ℤ)).map_comp, Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  have := NatTrans.congr_app hc (K.X n)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, leftUnitor_hom_app,
    rightUnitor_inv_app, Category.comp_id] at this
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexIdIso_hom_app_f, Functor.mapHomologicalComplex_map_f]
  erw [Category.comp_id, Category.comp_id]
  erw [Category.comp_id] at this
  exact this

variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

section NatIso

variable {F G H : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The isomorphism of left derived functors induced by the identity is the identity. -/
@[simp]
lemma leftDerivedFunctorNatIso_refl :
    F.leftDerivedFunctorNatIso (Iso.refl F) = Iso.refl _ := by
  ext : 1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono (F.leftDerivedFunctorCounit.app P),
    leftDerivedFunctorNatIso_hom_app_comp_counit]
  simp

end NatIso

section Comp

variable {F G H : C ⥤ C} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **Compatibility of the derived trivializations with composition**: for exact
endofunctors with trivializations `eF : F ≅ 𝟭`, `eG : G ≅ 𝟭` and `c : H ≅ F ⋙ G`, the
composite `L(H) ≅ L(F ⋙ G) ≅ L(F) ⋙ L(G) ≅ 𝟭` of the derived trivializations is the derived
trivialization of the composite `H ≅ F ⋙ G ≅ 𝟭`. -/
lemma leftDerivedFunctorIdIso_comp (eF : F ≅ 𝟭 C) (eG : G ≅ 𝟭 C) (c : H ≅ F ⋙ G) :
    H.leftDerivedFunctorNatIso c ≪≫ F.leftDerivedFunctorCompIso G ≪≫
        isoWhiskerRight (leftDerivedFunctorIdIso eF) G.leftDerivedFunctor ≪≫
        G.leftDerivedFunctor.leftUnitor ≪≫ leftDerivedFunctorIdIso eG =
      leftDerivedFunctorIdIso (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG) := by
  ext : 1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  have h₁ := leftDerivedFunctorIdIso_hom_app_Qh_obj eF P
  have hn := (leftDerivedFunctorIdIso eG).hom.naturality (Qh.map
    ((NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P))
  have h₂ := leftDerivedFunctorIdIso_hom_app_Qh_obj eG ((F.mapHomotopyCategory (.up ℤ)).obj P)
  have h₃ := leftDerivedFunctorIdIso_hom_app_Qh_obj
    (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG) P
  -- `leftDerivedFunctorIdIso` is reducible: generalize it so that `simp` does not unfold it.
  generalize leftDerivedFunctorIdIso eF = a at h₁ ⊢
  generalize leftDerivedFunctorIdIso eG = b at hn h₂ ⊢
  generalize leftDerivedFunctorIdIso (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG) = d
    at h₃ ⊢
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    leftUnitor_hom_app]
  erw [Category.id_comp]
  rw [h₁, Functor.map_comp, Category.assoc]
  rw [id_map] at hn
  erw [hn]
  rw [h₂, h₃, Category.assoc, leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, mapHomotopyCategory_isoId_comp]

end Comp

section Square

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

variable {F : C ⥤ C} {G : C ⥤ D} {F' : D ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

/-- **Compatibility of the derived trivializations with commutative squares**: for exact
functors `F : C ⥤ C`, `G : C ⥤ D`, `F' : D ⥤ D`, trivializations `eF : F ≅ 𝟭`, `eF' : F' ≅ 𝟭`
and an isomorphism `c : F ⋙ G ≅ G ⋙ F'` compatible with them, the induced isomorphism
`L(F) ⋙ L(G) ≅ L(F ⋙ G) ≅ L(G ⋙ F') ≅ L(G) ⋙ L(F')` is compatible with the derived
trivializations. -/
lemma leftDerivedFunctorIdIso_square (eF : F ≅ 𝟭 C) (eF' : F' ≅ 𝟭 D) (c : F ⋙ G ≅ G ⋙ F')
    (hc : c.hom ≫ whiskerLeft G eF'.hom = whiskerRight eF.hom G ≫ G.leftUnitor.hom ≫
      G.rightUnitor.inv) :
    (F.leftDerivedFunctorCompIso G).inv ≫ ((F ⋙ G).leftDerivedFunctorNatIso c).hom ≫
        (G.leftDerivedFunctorCompIso F').hom ≫
        whiskerLeft G.leftDerivedFunctor (leftDerivedFunctorIdIso eF').hom =
      whiskerRight (leftDerivedFunctorIdIso eF).hom G.leftDerivedFunctor ≫
        G.leftDerivedFunctor.leftUnitor.hom ≫ G.leftDerivedFunctor.rightUnitor.inv := by
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono (G.leftDerivedFunctorCounit.app P)]
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, leftUnitor_hom_app,
    rightUnitor_inv_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  have hn := (leftDerivedFunctorIdIso eF').hom.naturality (G.leftDerivedFunctorCounit.app P)
  rw [id_map] at hn
  erw [← hn]
  erw [leftDerivedFunctorIdIso_hom_app_Qh_obj eF' ((G.mapHomotopyCategory (.up ℤ)).obj P)]
  rw [leftDerivedFunctorIdIso_hom_app_Qh_obj eF P, G.leftDerivedFunctor.map_comp,
    Category.assoc]
  erw [leftDerivedFunctorCounit_naturality]
  rw [leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc,
    ← leftDerivedFunctorCompIso_hom_app_comp_counit, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp, mapHomotopyCategory_isoId_square eF eF' c hc]

end Square

end CategoryTheory.Functor
