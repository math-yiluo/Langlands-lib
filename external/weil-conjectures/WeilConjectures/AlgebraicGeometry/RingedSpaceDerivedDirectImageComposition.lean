/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic

/-!
# Composition of derived direct images of modules on ringed spaces

Source: Stacks Project, Cohomology, Lemma 20.28.2 (Tag 0D5T)
(blueprint: lem-pc-ringed-spaces-derived-direct-image-composition).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

set_option autoImplicit false

private theorem derivedCompositionOfAcyclic
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H = F ⋙ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :
    ∃ e : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor,
      ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
        HEq (H.rightDerivedFunctorUnit.app K ≫ e.inv.app (DerivedCategory.Qh.obj K))
          (G.rightDerivedFunctorUnit.app
              ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)) := by
  subst H
  let β := Functor.rightDerivedFunctorCompUnit F G
  have hβ : (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    have h₁ : IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := inferInstance
    have h₂ := h I
    dsimp only [β, Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let δ := (F ⋙ G).rightDerivedFunctor.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β
  have hδ : IsIso δ :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (F ⋙ G).rightDerivedFunctor
      (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β).mp hβ
  refine ⟨(asIso δ).symm, ?_⟩
  intro K
  apply heq_of_eq
  change (F ⋙ G).rightDerivedFunctorUnit.app K ≫ δ.app (DerivedCategory.Qh.obj K) = _
  rw [Functor.rightDerived_fac_app]
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [β, Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hcomp : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ _).obj L) = 𝟙 _ := by
    change (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  erw [hcomp, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem derivedCompositionOfAcyclic_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :
    ∃ e : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ (F ⋙ G).rightDerivedFunctor,
      ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
        (F ⋙ G).rightDerivedFunctorUnit.app K ≫ e.inv.app (DerivedCategory.Qh.obj K) =
          G.rightDerivedFunctorUnit.app
              ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  obtain ⟨e, he⟩ := derivedCompositionOfAcyclic F G (F ⋙ G) rfl h
  exact ⟨e, fun K ↦ eq_of_heq (he K)⟩

namespace AlgebraicGeometry.RingedSpace

private theorem moduleDirectImage_comp_eq {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDirectImage (f ≫ g) = moduleDirectImage f ⋙ moduleDirectImage g := rfl

/-- Derived direct images compose canonically. The inverse of the comparison is
characterized by compatibility with the right-derived units: its composite with the
unit for `(g ∘ f)_*` is the composite of the units for `g_*` and `f_*`. The underived
identification `(g ∘ f)_* = g_* ∘ f_*` is the identity on sections of inverse-image opens.
This specifies the canonical comparison rather than an arbitrary natural isomorphism.
Source: Stacks Project, Cohomology, Lemma 20.28.2 (Tag 0D5T)
(blueprint: lem-pc-ringed-spaces-derived-direct-image-composition).

Proof: by lem-pc-ringed-spaces-derived-adjoint-general (Tag 079W), derived pullback
is left adjoint to derived direct image for each of `f`, `g`, and `f ≫ g`.
By lem-pc-ringed-spaces-derived-pullback-composition (Tag 0D5S), the composite
`Lg^* ⋙ Lf^*` identifies canonically with `L(g ∘ f)^*`. Transport the adjunction for
the composite morphism across this identification. Then lem-cat-right-adjoint-composition
identifies its right adjoint with `Rf_* ⋙ Rg_*`; invert that identification to obtain
the displayed orientation. The mate construction is compatible with the underived
composition identification, so its inverse satisfies the displayed unit equation.
The right-derived universal property makes this equation characterize the comparison. -/
theorem exists_derivedModuleDirectImageComposition
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ e : derivedModuleDirectImage f ⋙ derivedModuleDirectImage g ≅
        derivedModuleDirectImage (f ≫ g),
      ∀ K : HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ),
        (moduleDirectImage (f ≫ g)).rightDerivedFunctorUnit.app K ≫
            e.inv.app (DerivedCategory.Qh.obj K) =
          (moduleDirectImage g).rightDerivedFunctorUnit.app
              (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            (derivedModuleDirectImage g).map
              ((moduleDirectImage f).rightDerivedFunctorUnit.app K) := by
  simpa only [derivedModuleDirectImage, moduleDirectImage_comp_eq] using
    derivedCompositionOfAcyclic_comp (moduleDirectImage f) (moduleDirectImage g)
      (isIso_moduleDirectImage_unit_on_kInjective f g)

end AlgebraicGeometry.RingedSpace
