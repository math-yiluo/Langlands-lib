/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Functoriality of the derived isomorphisms of exact functors

For exact functors between monoidal abelian categories with functorial flat resolutions, the
isomorphisms `L(F) ≅ L(G)` induced by isomorphisms `F ≅ G`
(`CategoryTheory.Functor.leftDerivedFunctorNatIso`) are compatible with composition and inverses,
and with the composition isomorphisms `L(F ⋙ G) ≅ L(F) ⋙ L(G)`
(`CategoryTheory.Functor.leftDerivedFunctorCompIso`).

## Main results

- `CategoryTheory.Functor.leftDerivedFunctorNatIso_trans`,
  `CategoryTheory.Functor.leftDerivedFunctorNatIso_symm`,
  `CategoryTheory.Functor.leftDerivedFunctorNatIso_isoWhiskerRight` and
  `CategoryTheory.Functor.leftDerivedFunctorNatIso_isoWhiskerLeft`.
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The derived isomorphism of a composite of isomorphisms of exact functors is the composite
of the derived isomorphisms. -/
lemma leftDerivedFunctorNatIso_trans {G H : C ⥤ D} [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (e₁ : F ≅ G) (e₂ : G ≅ H) :
    F.leftDerivedFunctorNatIso (e₁ ≪≫ e₂) =
      F.leftDerivedFunctorNatIso e₁ ≪≫ G.leftDerivedFunctorNatIso e₂ := by
  ext : 1
  simp [leftDerivedFunctorNatIso, mapDerivedCategoryNatIso_trans]

/-- The derived isomorphism of the inverse of an isomorphism of exact functors is the inverse of
the derived isomorphism. -/
lemma leftDerivedFunctorNatIso_symm {G : C ⥤ D} [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : F ≅ G) :
    G.leftDerivedFunctorNatIso e.symm = (F.leftDerivedFunctorNatIso e).symm := by
  ext : 1
  simp [leftDerivedFunctorNatIso, mapDerivedCategoryNatIso_symm]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- The composition isomorphism `L(F ⋙ G) ≅ L(F) ⋙ L(G)` is natural in the first functor: for
`e : F ≅ F'` the square
```
                 L(e ▷ G)
  L(F ⋙ G) ─────────────────▶ L(F' ⋙ G)
     │                            │
     ▼                            ▼
  L(F) ⋙ L(G) ──────────────▶ L(F') ⋙ L(G)
                L(e) ▷ L(G)
```
commutes, the vertical maps being the composition isomorphisms. -/
lemma leftDerivedFunctorNatIso_isoWhiskerRight {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ((F ⋙ G).leftDerivedFunctorNatIso (isoWhiskerRight e G)).hom ≫
        (F'.leftDerivedFunctorCompIso G).hom =
      (F.leftDerivedFunctorCompIso G).hom ≫
        Functor.whiskerRight (F.leftDerivedFunctorNatIso e).hom G.leftDerivedFunctor := by
  have h := mapDerivedCategoryNatIso_isoWhiskerRight e G
  ext K
  have hK := NatTrans.congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hK
  simp only [leftDerivedFunctorNatIso, leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, Functor.whiskerRight_app, isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% hK]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [← NatTrans.naturality]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Functor.comp_obj]

/-- The composition isomorphism `L(F ⋙ G) ≅ L(F) ⋙ L(G)` is natural in the second functor: for
`e : G ≅ G'` the square
```
                 L(F ◁ e)
  L(F ⋙ G) ─────────────────▶ L(F ⋙ G')
     │                            │
     ▼                            ▼
  L(F) ⋙ L(G) ──────────────▶ L(F) ⋙ L(G')
                L(F) ◁ L(e)
```
commutes, the vertical maps being the composition isomorphisms. -/
lemma leftDerivedFunctorNatIso_isoWhiskerLeft {G G' : D ⥤ E} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G'.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    ((F ⋙ G).leftDerivedFunctorNatIso (isoWhiskerLeft F e)).hom ≫
        (F.leftDerivedFunctorCompIso G').hom =
      (F.leftDerivedFunctorCompIso G).hom ≫
        Functor.whiskerLeft F.leftDerivedFunctor (G.leftDerivedFunctorNatIso e).hom := by
  have h := mapDerivedCategoryNatIso_isoWhiskerLeft F e
  ext K
  have hK := NatTrans.congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hK
  simp only [leftDerivedFunctorNatIso, leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, Functor.whiskerRight_app, isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hK, NatTrans.naturality_assoc]

end CategoryTheory.Functor
