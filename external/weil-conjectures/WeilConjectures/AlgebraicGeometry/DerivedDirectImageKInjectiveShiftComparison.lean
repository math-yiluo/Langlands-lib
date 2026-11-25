/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparisonAux

/-! # Shift compatibility of the identity-resolution comparison

Source: Stacks Project, Tag 079V, construction of the total derived direct image.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 8

noncomputable section
namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance



-- Whiskered shift comparisons involve several localized functors.
/-- The identity-resolution computation intertwines the actual derived shift comparison.
Source: Stacks Project, Tag 079V, construction by the equivalence K(Inj) to D.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift).

Proof: Restrict the right-derived unit to the homotopy category of K-injective
complexes. Its components are invertible. The isomorphism from the right derived
functor to the inverse K-injective equivalence followed by termwise direct image
is constructed by this restricted unit and the equivalence counit. The shift
structure of the right derived functor is transported along exactly this
isomorphism. Thus the restricted unit commutes with shifts. Whisker with the
homotopy quotient, then insert quotientCompQhIso and mapHomotopyCategoryFactors.
Their shift compatibilities identify the termwise localized shift comparison
with moduleDirectImageLocalizedShiftIso. Invert the K-injective computation
components and cancel the localized inverse shift map; the resulting component
equation is the displayed formula. This proof requires only K and K[1] to be
K-injective and applies to every morphism of ringed spaces; there is no cover,
short exact sequence or connecting map in the assertion. -/
theorem derivedModuleDirectImageKInjectiveIso_shift
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app K) ≫
      (derivedModuleDirectImageKInjectiveIso g (K⟦(1 : ℤ)⟧)).hom ≫
      (moduleDirectImageLocalizedShiftIso g K).hom =
    ((derivedModuleDirectImage g).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (derivedModuleDirectImageKInjectiveIso g K).hom⟦(1 : ℤ)⟧'  := by
  rw [← Category.assoc, derivedModuleDirectImageKInjectiveIso_shift_aux]
  simp

end AlgebraicGeometry.RingedSpace
