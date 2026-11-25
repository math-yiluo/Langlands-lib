/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMate
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Invertibility of the derived base change map

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions of additive functors between abelian
categories with exact left adjoints `F : D ⥤ C` and `F' : D' ⥤ C'`, and let `N_D : D ⥤ D'`,
`N_C : C ⥤ C'` be exact functors with an isomorphism `α : N_D ⋙ F' ≅ F ⋙ N_C`. The mate of
the induced isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` under the derived adjunctions
`D(F) ⊣ RG` and `D(F') ⊣ RG'` is the derived base change map `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'`.

We show that it is an isomorphism as soon as the underived base change map
`G ⋙ N_D ⟶ N_C ⋙ G'` (the mate of `α`) is an isomorphism and `N_C` preserves K-injective
complexes (`CategoryTheory.Adjunction.isIso_mateEquiv_mapDerivedCategorySquareIso`): on a
K-injective complex `I`, both `RG (Q I)` and `RG' (Q (N_C I))` are computed without resolving,
and the derived base change map is the image of the underived one
(`CategoryTheory.UnboundedExactTower.localized_mate_cochain_normalization`).

When `F'` is only given through its total left derived functor `LF'` (with the derived
adjunction `LF' ⊣ RG'`), the square is `CategoryTheory.Functor.leftDerivedFunctorSquareIso α :
D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)`, and its mate is again invertible
(`CategoryTheory.Adjunction.isIso_mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso`).
On complexes, this square is the counit of `LF'` followed by the image of `α`
(`CategoryTheory.Functor.leftDerivedFunctorSquareIso_hom_app_Q_obj`,
`CategoryTheory.Functor.whiskerLeft_Q_leftDerivedFunctorSquareIso_hom`).
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions C']
  {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] [N_D.Additive] [N_C.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C]

/-- **Invertibility of the derived base change map.** If the underived base change map
`G ⋙ N_D ⟶ N_C ⋙ G'` (the mate of `α`) is an isomorphism and `N_C` preserves K-injective
complexes, then the derived base change map `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'`, the mate of the
isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced by `α` under the derived adjunctions
`D(F) ⊣ RG` and `D(F') ⊣ RG'`, is an isomorphism. -/
theorem isIso_mateEquiv_mapDerivedCategorySquareIso (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : N_D ⋙ F' ≅ F ⋙ N_C) [N_C.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' α.hom)] :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso α).hom) := by
  let β := (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategorySquareIso α).hom)
  have hI (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      IsIso (β.app (DerivedCategory.Q.obj I)) := by
    have : CochainComplex.IsKInjective ((N_C.mapHomologicalComplex (.up ℤ)).obj I) :=
      Functor.PreservesKInjectiveComplexes.isKInjective_map I
    have h := UnboundedExactTower.localized_mate_cochain_normalization adj adj' α I
    have hu : IsIso (UnboundedExactTower.cochainUnit G I) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hu' : IsIso (UnboundedExactTower.cochainUnit G'
        ((N_C.mapHomologicalComplex (.up ℤ)).obj I)) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hc : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' α.hom) (.up ℤ)).app I) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv adj adj' α.hom)) (.up ℤ)).hom.app I))
    have ht : IsIso (N_D.mapDerivedCategoryFactors.inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        N_D.mapDerivedCategory.map (UnboundedExactTower.cochainUnit G I) ≫
        β.app (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (N_C.mapDerivedCategoryFactors.hom.app I)) := by
      dsimp only [UnboundedExactTower.localizedSquare] at h
      dsimp only [β]
      rw [h]
      infer_instance
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using ht
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ β fun K ↦ ?_
  obtain ⟨I, hIi, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI I hIi
  have hs : IsIso ((G.rightDerivedFunctor ⋙ N_D.mapDerivedCategory).map e.hom ≫
      β.app (DerivedCategory.Q.obj I)) := inferInstance
  rw [β.naturality e.hom] at hs
  exact IsIso.of_isIso_comp_right (β.app K)
    ((N_C.mapDerivedCategory ⋙ G'.rightDerivedFunctor).map e.hom)

section LeftDerived

variable [MonoidalCategory D'] [MonoidalPreadditive D'] [HasCountableCoproducts D']
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D'] [HasExactColimitsOfShape ℤ D']
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').obj X)]
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D']

/-- The isomorphism `D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)` induced by `α : N_D ⋙ F' ≅ F ⋙ N_C`, where
`LF'` is the total left derived functor of the exact functor `F'`: the identification
`LF' ≅ D(F')` (`CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`) followed by the
isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced by `α`. -/
noncomputable def _root_.CategoryTheory.Functor.leftDerivedFunctorSquareIso
    (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    N_D.mapDerivedCategory ⋙ F'.leftDerivedFunctor ≅
      F.mapDerivedCategory ⋙ N_C.mapDerivedCategory :=
  Functor.isoWhiskerLeft _ F'.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso α

/-- The mate of `CategoryTheory.Functor.leftDerivedFunctorSquareIso α` under `D(F) ⊣ RG` and the
derived adjunction `LF' ⊣ RG'` is the mate of `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` under
`D(F) ⊣ RG` and `D(F') ⊣ RG'`. -/
lemma mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction adj'.derivedAdjunction
      (Functor.leftDerivedFunctorSquareIso α).hom) =
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategorySquareIso α).hom) := by
  rw [derivedAdjunction_eq_ofNatIsoLeft]
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit, Functor.leftDerivedFunctorSquareIso]

/-- **Invertibility of the derived base change map**, for the derived adjunction `LF' ⊣ RG'`:
if the underived base change map `G ⋙ N_D ⟶ N_C ⋙ G'` is an isomorphism and `N_C` preserves
K-injective complexes, then the mate `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'` of
`CategoryTheory.Functor.leftDerivedFunctorSquareIso α` is an isomorphism. -/
theorem isIso_mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso (adj : F ⊣ G)
    (adj' : F' ⊣ G') (α : N_D ⋙ F' ≅ F ⋙ N_C) [N_C.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' α.hom)] :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction adj'.derivedAdjunction
      (Functor.leftDerivedFunctorSquareIso α).hom) := by
  rw [mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso]
  exact isIso_mateEquiv_mapDerivedCategorySquareIso adj adj' α

end LeftDerived

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
  [F.Additive] [F'.Additive] [N_D.Additive] [N_C.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits F']
  [PreservesFiniteColimits F'] [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C] in
/-- The termwise isomorphism `F'(N_D P) ≅ N_C(F P)` of complexes induced by
`α : N_D ⋙ F' ≅ F ⋙ N_C`, written with the composition isomorphisms
`Functor.mapHomologicalComplexCompIso`, is the image of `α` under
`NatTrans.mapHomologicalComplex`. -/
lemma mapHomologicalComplexCompIso_comp_inv_app (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
        (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P =
      (NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app P := by
  ext n
  exact Category.comp_id _

/-- On the image `Q P` of a complex, the isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced
by `α : N_D ⋙ F' ≅ F ⋙ N_C` is, up to the factorizations `Functor.mapDerivedCategoryFactors`
through `Q`, the image under `Q` of the termwise isomorphism `α`. -/
@[reassoc]
lemma mapDerivedCategorySquareIso_hom_app_Q_obj (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (mapDerivedCategorySquareIso α).hom.app (DerivedCategory.Q.obj P) ≫
        N_C.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      F'.mapDerivedCategory.map (N_D.mapDerivedCategoryFactors.hom.app P) ≫
        F'.mapDerivedCategoryFactors.hom.app ((N_D.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
          (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P) := by
  rw [mapHomologicalComplexCompIso_comp_inv_app]
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have hc := mapDerivedCategoryCompIso_fac F N_C P
  have hc' := mapDerivedCategoryCompIso_fac N_D F' P
  have hi : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).hom.app P = 𝟙 _ := rfl
  have hi' : (mapHomologicalComplexCompIso (Iso.refl (N_D ⋙ F')) (.up ℤ)).hom.app P = 𝟙 _ :=
    rfl
  erw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [hi', CategoryTheory.Functor.map_id, Category.comp_id] at hc'
  erw [hc, mapDerivedCategoryNatIso_fac]
  erw [← hc']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

variable [MonoidalCategory D'] [MonoidalPreadditive D'] [HasCountableCoproducts D']
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D'] [HasExactColimitsOfShape ℤ D']
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').obj X)]
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D']

/-- On the image `Q P` of a complex, the isomorphism `D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)` of
`CategoryTheory.Functor.leftDerivedFunctorSquareIso α` is, up to the factorizations through `Q`
and `Qh`, the counit of `LF'` at `N_D P` followed by the image under `Q` of the termwise
isomorphism `α`:
```
LF' (D(N_D) (Q P)) ──α──▶ D(N_C) (D(F) (Q P))
       │                         │
LF' (Qh (N_D P))           Q (N_C (F P))
       │ counit                  ▲
       ▼                         │ Q(α_P)
Qh (F' (N_D P)) ════════ Q (F' (N_D P))
``` -/
@[reassoc]
lemma leftDerivedFunctorSquareIso_hom_app_Q_obj (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (leftDerivedFunctorSquareIso α).hom.app (DerivedCategory.Q.obj P) ≫
        N_C.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      F'.leftDerivedFunctor.map (N_D.mapDerivedCategoryFactors.hom.app P ≫
          (DerivedCategory.quotientCompQhIso D').inv.app
            ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F'.leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient D' (.up ℤ)).obj ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (DerivedCategory.quotientCompQhIso C').hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
          (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P) := by
  have h₁ := mapDerivedCategorySquareIso_hom_app_Q_obj α P
  have h₂ := F'.leftDerivedFunctorIsoMapDerivedCategory_hom_app_quotient_obj
    ((N_D.mapHomologicalComplex (.up ℤ)).obj P)
  have h₃ := F'.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (N_D.mapDerivedCategoryFactors.hom.app P ≫
      (DerivedCategory.quotientCompQhIso D').inv.app ((N_D.mapHomologicalComplex (.up ℤ)).obj P))
  simp only [leftDerivedFunctorSquareIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% h₂, reassoc_of% h₃]
  simpa [← Functor.map_comp_assoc] using h₁

/-- **The isomorphism `CategoryTheory.Functor.leftDerivedFunctorSquareIso α` on complexes**, as an
identity of natural transformations of functors `CochainComplex D ℤ ⥤ DerivedCategory C'`: after
precomposition with `Q`, it is the counit of `LF'` on `N_D P` followed by the image under `Q` of
the termwise isomorphism `α`, all functors being composed explicitly (with associators). This
is the form of `CategoryTheory.Functor.leftDerivedFunctorSquareIso_hom_app_Q_obj` in which no
identification of objects by definitional unfolding is needed, so it can be instantiated with
concrete functors at no cost. -/
lemma whiskerLeft_Q_leftDerivedFunctorSquareIso_hom (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    whiskerLeft DerivedCategory.Q (leftDerivedFunctorSquareIso α).hom =
      (Functor.associator _ _ _).inv ≫
      whiskerRight N_D.mapDerivedCategoryFactors.hom F'.leftDerivedFunctor ≫
      whiskerRight (whiskerLeft (N_D.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso D').inv) F'.leftDerivedFunctor ≫
      whiskerRight (Functor.associator _ _ _).inv F'.leftDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ F'.leftDerivedFunctorCounit ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.associator _ _ _).hom DerivedCategory.Qh ≫
      whiskerRight (whiskerLeft (N_D.mapHomologicalComplex (.up ℤ))
        (F'.mapHomotopyCategoryFactors (.up ℤ)).hom) DerivedCategory.Qh ≫
      whiskerRight (Functor.associator _ _ _).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ (DerivedCategory.quotientCompQhIso C').hom ≫
      whiskerRight (mapHomologicalComplexCompIso α (.up ℤ)).hom DerivedCategory.Q ≫
      (F ⋙ N_C).mapDerivedCategoryFactors.inv ≫
      whiskerLeft DerivedCategory.Q (mapDerivedCategoryCompIso F N_C).inv := by
  ext P
  have h₁ := leftDerivedFunctorSquareIso_hom_app_Q_obj α P
  have h₂ := mapDerivedCategoryCompIso_fac F N_C P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Functor.comp_obj, Category.id_comp, Functor.map_id]
  have h₃ : (F'.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((N_D.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  rw [
    ← cancel_mono (D(N_C).map (F.mapDerivedCategoryFactors.hom.app P) ≫
      N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).hom.app P))]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, h₂, Iso.inv_hom_id_app]
  simp [h₃]

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On the image `Qh P` of an object of the homotopy category, the isomorphism
`D(F) ⋙ D(G) ≅ D(F') ⋙ D(G')` induced by `e : F ⋙ G ≅ F' ⋙ G'` is the image of the morphism
induced by `e` on homotopy categories, up to the factorization isomorphisms. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj_factorsh
    {C D E Z : Type*} [Category* C] [Category* D] [Category* E] [Category* Z]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory Z]
    (F : C ⥤ D) (G : D ⥤ Z) (F' : C ⥤ E) (G' : E ⥤ Z)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj P) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactorsh.hom.app P) ≫
        G'.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fach F' G' P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [hc, Functor.mapDerivedCategoryNatIso_fach]
  have hc := Functor.mapDerivedCategoryCompIso_fach F G P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [← hc]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]

section

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]

/-- The morphism induced on homotopy categories by the mate of a square is the mate, computed
with the adjunction induced on homotopy categories, of the morphism induced by the square. -/
lemma mapHomotopyCategory_mateEquiv_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') (K : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K =
      (adj'.mapHomotopyCategory (.up ℤ)).unit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app
            ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((G'.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C₄ (.up ℤ)).map _ =
    (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₄ (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map]
  exact congrArg (fun t ↦ _ ≫ _ ≫ t) (Category.comp_id _)

end

section

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [Abelian.HasKInjectiveResolutions C₁] [Abelian.HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- On the image of an object `K` of the homotopy category, precomposed with the unit of `R(R)`,
the mate of a square `θ : D(G) ⋙ D(L') ⟶ D(L) ⋙ D(G')` under the derived adjunctions
`D(L) ⊣ R(R)` and `D(L') ⊣ R(R')` is the image of the underived mate `R ⋙ G ⟶ G' ⋙ R'` of
`σ`, followed by the unit of `R(R')`, provided `θ` is induced by `σ` on homotopy
categories (`hθ`). -/
lemma mapDerivedCategoryRightDerivedAdjunction_mateEquiv_app_fac (adj : L ⊣ R)
    (adj' : L' ⊣ R') (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      G'.mapDerivedCategory)
    (hθ : ∀ N : HomotopyCategory C₂ (.up ℤ),
      θ.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N))
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app
          (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) := by
  have hmate (Z : DerivedCategory C₁) :
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app Z =
        adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
            (G.mapDerivedCategory.obj (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (θ.app (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (G'.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app Z)) := by
    simp [mateEquiv_apply]
  set N := (R.mapHomotopyCategory (.up ℤ)).obj K
  set u := R.rightDerivedFunctorUnit.app K
  have h₁ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map u)
  have h₂ := θ.naturality u
  have h₃ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit K
  change L.mapDerivedCategory.map u ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj K) =
    _ at h₃
  have h₄ := mapHomotopyCategory_mateEquiv_app adj adj' σ K
  have h₅ := R'.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N ≫
      (G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K))
  have h₆ := (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C₄ (.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
    R'.rightDerivedFunctorUnit ((G.mapHomotopyCategory (.up ℤ)).obj N)
  change adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj N)) ≫ _ = _ at h₆
  have h₇ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategoryFactorsh.hom.app N)
  have h₈ := hθ N
  have h₉ := G'.mapDerivedCategoryFactorsh.hom.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₅ h₇ h₉
  rw [hmate, reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp (G'.mapDerivedCategory), h₃]
  erw [h₄]
  erw [← Functor.map_comp (R'.mapHomotopyCategory (.up ℤ))]
  erw [Functor.map_comp DerivedCategory.Qh, Category.assoc, reassoc_of% h₅]
  erw [← reassoc_of% h₆, reassoc_of% h₇]
  congr 1
  have key : θ.app (DerivedCategory.Qh.obj N) ≫
      G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N) ≫
        DerivedCategory.Qh.map
          ((G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) ≫
        G'.mapDerivedCategoryFactorsh.inv.app K := by
    rw [← cancel_mono (G'.mapDerivedCategoryFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    rw [h₉, reassoc_of% h₈]
    erw [Category.comp_id]
  rw [key]
  simp only [Functor.map_comp]
  simp only [Category.assoc]

/-- **The derived base change morphism on the homotopy category.** Precomposed with the unit of
`R(R)`, the derived base change morphism `R(R) ⋙ D(G) ⟶ D(G') ⋙ R(R')` (the mate of the
isomorphism `D(G) ⋙ D(L') ≅ D(L) ⋙ D(G')` induced by `e : G ⋙ L' ≅ L ⋙ G'`) is the image of
the underived base change morphism `R ⋙ G ⟶ G' ⋙ R'` (the mate of `e`), followed by the unit
of `R(R')`. -/
lemma derivedBaseChange_app_fac (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ G')
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (adj.derivedBaseChange adj' e).app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) :=
  mapDerivedCategoryRightDerivedAdjunction_mateEquiv_app_fac adj adj' _ _
    (mapDerivedCategorySquareIso_hom_app_Qh_obj_factorsh G L' L G' e) K

/-- **Invertibility of the derived base change morphism.** If the underived base change
morphism `R ⋙ G ⟶ G' ⋙ R'` (the mate of `e : G ⋙ L' ≅ L ⋙ G'`) is an isomorphism and `G'`
preserves K-injective complexes, then the derived base change morphism
`R(R) ⋙ D(G) ⟶ D(G') ⋙ R(R')` is an isomorphism. -/
theorem isIso_derivedBaseChange_app (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ G')
    [G'.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom))]
    (M : DerivedCategory C₁) :
    IsIso ((adj.derivedBaseChange adj' e).app M) := by
  let β := mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)
  let eh : (R ⋙ G).mapHomotopyCategory (.up ℤ) ≅ (G' ⋙ R').mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory β _
      inv := NatTrans.mapHomotopyCategory (inv β) _
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have : IsIso (NatTrans.mapHomotopyCategory
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) (.up ℤ)) := eh.isIso_hom
  obtain ⟨K₀, ⟨eK⟩⟩ : ∃ K₀ : CochainComplex C₁ ℤ, Nonempty (DerivedCategory.Q.obj K₀ ≅ M) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso M⟩⟩
  obtain ⟨I, _, i, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K₀
  rw [NatTrans.isIso_app_iff_of_iso _ (eK.symm ≪≫ asIso (DerivedCategory.Q.map i) ≪≫
    ((DerivedCategory.quotientCompQhIso C₁).app I).symm :
    M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))]
  have : IsIso (R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj I))) :=
    inferInstanceAs (IsIso (R'.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
      ((G'.mapHomologicalComplex (.up ℤ)).obj I))))
  have : IsIso (G.mapDerivedCategory.map
      (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        (adj.derivedBaseChange adj' e).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    rw [derivedBaseChange_app_fac]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.mapDerivedCategory.map
    (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I))) _

end

end CategoryTheory.Adjunction
