/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCounitEquation
@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Intermediate compatibility equation for transported derived counits.
Source: Stacks Project, Tag 06Y6.
Proof: this intermediate statement packages the corresponding derived-category
localization transport step; the proof is deferred for independent parallel work.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-compatibility). -/
theorem raw_compatibility
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    ∀ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
      (q : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E ≅
        (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh))
      (t : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ) ≅
        (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ)),
      ∃ a : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L₀ ≅
        HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L ⋙ E,
        ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
          a.hom.app K ≫ E.map (ε.app
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj K)) ≫
            q.hom.app (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj K) =
          ε₀.app ((HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)).obj
            (((restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)) ≫
            ((HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh).map
              (t.hom.app K)) := by
  have _ := hRB
  exact raw_transport_counit_equation
    (extendScalars (algebraMap R₀ B₀)) (extendScalars (algebraMap R B))
    L₀ L ε₀ ε h₀ h
    (restrictScalarsEquivalenceOfRingEquiv eR) (restrictScalarsEquivalenceOfRingEquiv eB)
end ModuleCat
