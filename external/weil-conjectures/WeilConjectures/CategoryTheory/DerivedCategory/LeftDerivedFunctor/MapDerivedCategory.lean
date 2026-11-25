/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The total left derived functor of an exact functor is `mapDerivedCategory`

An exact functor `F : C ⥤ D` between abelian categories induces a functor
`F.mapDerivedCategory : DerivedCategory C ⥤ DerivedCategory D` directly, by applying `F`
levelwise (`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`). When the monoidal
abelian category `C` moreover admits functorial flat resolutions, `F` also has a total
left derived functor `F.leftDerivedFunctor` computed via K-flat resolutions
(`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`). This file shows that
the two constructions agree:

- `Functor.leftDerivedFunctorIsoMapDerivedCategory`: the canonical isomorphism
  `F.leftDerivedFunctor ≅ F.mapDerivedCategory`, obtained from uniqueness of left derived
  functors: since the comparison `F.mapDerivedCategoryFactorsh` is an isomorphism,
  `F.mapDerivedCategory` is *itself* a left derived functor of
  `F.mapHomotopyCategory ⋙ Qh`.
- `Functor.isIso_leftDerivedFunctorCounit`: consequently, the counit of the left derived
  functor of an exact functor is an isomorphism everywhere (not only on K-flat
  complexes).

From this compatibility we derive, still for exact functors, the isomorphisms expressing
that left derivation commutes with the constructions preserved by `mapDerivedCategory`
(themselves in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
`Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso` and
`Functor.mapDerivedCategoryHomologyFunctorIso`):

- `Functor.leftDerivedFunctorNatIso`, `Functor.leftDerivedFunctorCompIso`,
  `Functor.leftDerivedFunctorHomologyFunctorIso`,
  `Functor.singleFunctorCompLeftDerivedFunctorIso`: the corresponding statements for the
  total left derived functor, obtained by transport along the compatibility isomorphism.
- `Functor.PreservesKFlatComplexes` and `Functor.leftDerivedFunctorCompMapDerivedCategoryIso`:
  the composition isomorphism `L(F ⋙ G) ≅ D(F) ⋙ LG` for an exact `F` sending K-flat complexes
  to K-flat complexes and an arbitrary `G` preserving K-flat quasi-isomorphisms: left deriving
  such a composite amounts to applying `F` levelwise and left deriving `G`. This is what
  identifies the derived pullback `Lf^* = L(Ext_{α_f} ∘ mapMod(f^*))` on module objects over a
  coefficient sheaf with `L(Ext_{α_f}) ∘ D(mapMod(f^*))`.

These are the general inputs needed to identify the derived pullback `Lg^*` of étale
sheaves (which is left derived from the *exact* functor `g^*`) with the levelwise
functor, and to obtain its composition, homology, and single-degree compatibilities; see
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

section PreservesKFlatComplexes

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- An additive functor `F : C ⥤ D` between monoidal abelian categories *preserves K-flat
complexes* if it sends K-flat cochain complexes to K-flat cochain complexes. Together with
exactness, this is the hypothesis under which the left derived functor of a composite
`F ⋙ G` is `D(F) ⋙ LG`, see `Functor.leftDerivedFunctorCompMapDerivedCategoryIso`. -/
class PreservesKFlatComplexes (F : C ⥤ D) [F.Additive] : Prop where
  kFlat_map (K : CochainComplex C ℤ) (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

lemma kFlat_mapHomologicalComplex_obj (F : C ⥤ D) [F.Additive] [F.PreservesKFlatComplexes]
    (K : CochainComplex C ℤ) (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  PreservesKFlatComplexes.kFlat_map K hK

/-- If `F` is exact and preserves K-flat complexes and `G` preserves K-flat
quasi-isomorphisms, then so does `F ⋙ G`. -/
instance preservesKFlatQuasiIso_comp {E : Type uE} [Category.{vE} E] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.PreservesHomology]
    [F.PreservesKFlatComplexes] [G.PreservesKFlatQuasiIso] :
    (F ⋙ G).PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ :=
    G.quasiIso_mapHomologicalComplex_map_of_kFlat (F.kFlat_mapHomologicalComplex_obj _ hK)
      (F.kFlat_mapHomologicalComplex_obj _ hL) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)

end PreservesKFlatComplexes

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

section Compatibility

/-- For an *exact* functor `F` between abelian categories, the total left derived
functor computed via K-flat resolutions is canonically isomorphic to the functor
`F.mapDerivedCategory` induced by applying `F` levelwise. Indeed, since
`F.mapDerivedCategoryFactorsh` is an isomorphism, `F.mapDerivedCategory` is itself a
left derived functor of `F.mapHomotopyCategory ⋙ Qh`, and left derived functors are
unique up to canonical isomorphism. -/
noncomputable def leftDerivedFunctorIsoMapDerivedCategory :
    F.leftDerivedFunctor ≅ F.mapDerivedCategory :=
  leftDerivedUnique F.mapDerivedCategory F.leftDerivedFunctor F.leftDerivedFunctorCounit
    F.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[reassoc (attr := simp)]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_fac :
    Functor.whiskerLeft DerivedCategory.Qh F.leftDerivedFunctorIsoMapDerivedCategory.hom ≫
      F.mapDerivedCategoryFactorsh.hom = F.leftDerivedFunctorCounit := by
  simp [leftDerivedFunctorIsoMapDerivedCategory]

/-- The counit of the total left derived functor of an *exact* functor is an isomorphism
everywhere: the left derived functor is computed by applying the functor levelwise, with
no resolution needed. -/
instance isIso_leftDerivedFunctorCounit : IsIso F.leftDerivedFunctorCounit := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  infer_instance

/-- An isomorphism `F ≅ G` of exact functors induces an isomorphism
`F.leftDerivedFunctor ≅ G.leftDerivedFunctor` of the total left derived functors. -/
noncomputable def leftDerivedFunctorNatIso {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.leftDerivedFunctor ≅ G.leftDerivedFunctor :=
  F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryNatIso e ≪≫
    G.leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The total left derived functor of an exact functor commutes with the homology
functors: the canonical isomorphism
`H^n(-) ⋙ F ≅ F.leftDerivedFunctor ⋙ H^n(-)` of functors `DerivedCategory C ⥤ D`. -/
noncomputable def leftDerivedFunctorHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.leftDerivedFunctor ⋙ DerivedCategory.homologyFunctor D n :=
  F.mapDerivedCategoryHomologyFunctorIso n ≪≫
    isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm
      (DerivedCategory.homologyFunctor D n)

/-- The total left derived functor of an exact functor commutes with the single-degree
embeddings: the canonical isomorphism
`(-)[0] ⋙ F.leftDerivedFunctor ≅ F ⋙ (-)[0]` of functors `C ⥤ DerivedCategory D`. -/
noncomputable def singleFunctorCompLeftDerivedFunctorIso :
    DerivedCategory.singleFunctor C 0 ⋙ F.leftDerivedFunctor ≅
      F ⋙ DerivedCategory.singleFunctor D 0 :=
  isoWhiskerLeft (DerivedCategory.singleFunctor C 0)
      F.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    F.mapDerivedCategorySingleFunctor 0

/-- The total left derived functor of an additive equivalence of abelian categories is an
equivalence of derived categories: it is isomorphic to `F.mapDerivedCategory`. -/
instance isEquivalence_leftDerivedFunctor [F.IsEquivalence] : F.leftDerivedFunctor.IsEquivalence :=
  isEquivalence_of_iso F.leftDerivedFunctorIsoMapDerivedCategory.symm

end Compatibility

section Composition

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

/-- The composition isomorphism
`(F ⋙ G).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ G.leftDerivedFunctor` for exact
functors between abelian categories with functorial flat resolutions, obtained from
`mapDerivedCategoryCompIso` by transport along the compatibility isomorphisms. -/
noncomputable def leftDerivedFunctorCompIso (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ G.leftDerivedFunctor :=
  (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory ≪≫ (mapDerivedCategoryCompIso F G).symm ≪≫
    isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm G.mapDerivedCategory ≪≫
    isoWhiskerLeft F.leftDerivedFunctor G.leftDerivedFunctorIsoMapDerivedCategory.symm


section CompositionKFlat

variable (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso] [F.PreservesKFlatComplexes]

/-- The counit exhibiting `D(F) ⋙ LG` as a candidate left derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`, for an exact functor `F` preserving K-flat complexes: it
is assembled from the comparison `F.mapDerivedCategoryFactorsh`, the counit of `LG` and the
composition isomorphism of `mapHomotopyCategory`. -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryCounit :
    DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) ⟶
      (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom G.leftDerivedFunctor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) G.leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh

/-- If `F` is exact and preserves K-flat complexes, then `D(F) ⋙ LG`, equipped with the counit
`leftDerivedFunctorCompMapDerivedCategoryCounit`, is a left derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`: by the K-flat left derivability structure it suffices that
the counit is an isomorphism on K-flat complexes, which holds since `D(F)` is computed
levelwise and the counit of `LG` is an isomorphism on the K-flat complex `F K`. -/
instance isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor :
    (F.mapDerivedCategory ⋙ G.leftDerivedFunctor).IsLeftDerivedFunctor
      (leftDerivedFunctorCompMapDerivedCategoryCounit F G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  rw [(F ⋙ G).isLeftDerivedFunctor_iff_isIso_app_of_kFlat]
  intro K hK
  have h : IsIso (G.leftDerivedFunctorCounit.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) :=
    G.isIso_leftDerivedFunctorCounit_app_of_kFlat _ (F.kFlat_mapHomologicalComplex_obj K hK)
  dsimp only [leftDerivedFunctorCompMapDerivedCategoryCounit, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app]
  infer_instance

/-- **Composition with an exact functor preserving K-flat complexes**: for an exact functor
`F : C ⥤ D` preserving K-flat complexes and an additive functor `G : D ⥤ E` preserving K-flat
quasi-isomorphisms, `L(F ⋙ G) ≅ D(F) ⋙ LG`: the left derived functor of the composite is
computed by applying `F` levelwise and then `LG`. This is the left derived counterpart of
`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`, the K-flat preservation hypothesis
replacing the (automatic) preservation of acyclicity by the exact functor. -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryIso :
    (F ⋙ G).leftDerivedFunctor ≅ F.mapDerivedCategory ⋙ G.leftDerivedFunctor :=
  leftDerivedUnique (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) (F ⋙ G).leftDerivedFunctor
    (F ⋙ G).leftDerivedFunctorCounit (leftDerivedFunctorCompMapDerivedCategoryCounit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end CompositionKFlat

end Composition

end CategoryTheory.Functor
