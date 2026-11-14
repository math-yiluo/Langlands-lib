import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullbackDerived
import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomSingle

/-! # Singleton forms of the relative pullback comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.Cohomology.DerivedSectionsHomComparison

universe wC wA vC vA uC uA

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {A : Type uA} [Category.{vC} A] [Abelian A] [HasDerivedCategory.{max vC wA} A]
  (U : C ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option autoImplicit false

/-- Localizing the exact image of a singleton complex. -/
def singleComplexDerivedIso (M : C) :
    DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M)) ≅
      (DerivedCategory.singleFunctor A 0).obj (U.obj M) :=
  DerivedCategory.Q.mapIso ((U.mapCochainComplexSingleFunctor 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app (U.obj M)).symm

lemma singleMapDerivedIso_singlePlusQIso (M : C) :
    (singleMapDerivedIso U M).inv ≫
      U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        ((DerivedPlus.singlePlusQIso C).hom.app M)) ≫
      U.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C).hom.app
        ((DerivedPlus.singlePlusFunctor C).obj M)) ≫
      U.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj M) =
    (singleComplexDerivedIso U M).inv := by
  simp only [singleMapDerivedIso, DerivedPlus.singlePlusQIso, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [← U.mapDerivedCategory.map_comp_assoc, ← U.mapDerivedCategory.map_comp_assoc]
  simp only [Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [U.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  simp only [singleComplexDerivedIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, Category.id_comp]

variable [EnoughInjectives C]
  {D : Type uA} [Category.{vA} D] [Abelian D] [HasDerivedCategory.{wC} D]
  (F : C ⥤ D) [F.Additive]
  (G : D ⥤ AddCommGrpCat.{vC}) [G.Additive] [G.PreservesHomology]
  (Z : A) (e : F ⋙ G ≅ U ⋙ preadditiveCoyoneda.obj (op Z))

lemma comparisonOnComplex_singlePlus (M : C) (n : ℤ)
    (y : (derivedSections.{wA} F G n).obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj M))
    (a : ShiftedHom ((DerivedCategory.singleFunctor A 0).obj Z)
      ((DerivedCategory.singleFunctor A 0).obj (U.obj M)) n)
    (ha : (comparison.{wA} F G U Z e n).app
      ((DerivedCategory.Plus.singleFunctor C 0).obj M) y =
        a ≫ (singleMapDerivedIso U M).inv⟦n⟧') :
    (comparisonOnComplex.{wA} F G U Z e n).app
      ((DerivedPlus.singlePlusFunctor C).obj M)
      ((derivedSections.{wA} F G n).map
        ((DerivedPlus.singlePlusQIso C).hom.app M) y) =
      a ≫ (singleComplexDerivedIso U M).inv⟦n⟧' := by
  have hnat := ConcreteCategory.congr_hom
    ((comparison.{wA} F G U Z e n).naturality
      ((DerivedPlus.singlePlusQIso C).hom.app M)) y
  simp only [ConcreteCategory.comp_apply] at hnat
  change (comparison.{wA} F G U Z e n).app _
      ((derivedSections.{wA} F G n).map
        ((DerivedPlus.singlePlusQIso C).hom.app M) y) ≫
      (U.mapDerivedCategory.map
        ((DerivedCategory.Plus.QCompιIso C).hom.app
          ((DerivedPlus.singlePlusFunctor C).obj M)) ≫
        U.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor C 0).obj M))⟦n⟧' = _
  erw [hnat]
  change ((comparison.{wA} F G U Z e n).app _ y ≫
      (U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        ((DerivedPlus.singlePlusQIso C).hom.app M)))⟦n⟧') ≫ _ = _
  rw [ha]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [singleMapDerivedIso_singlePlusQIso]

end Langlands.Cohomology.DerivedSectionsHomComparison

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic DerivedSectionsHomComparison
open AbelianSheafDerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X : Over (Spec R)}

/-- A sheaf cohomology class in the singleton relative-derived-sections model. -/
def relativeSingleDerivedSectionsClass (M : X.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj M) n) :
    (derivedSections.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).obj
        ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).obj M) :=
  ULift.up ((DerivedPlus.homologyIso (DerivedSections.relativeGlobalSections X.hom)
    (injectiveResolution M) n).inv (relativeHAddEquiv X.hom M n x))

lemma relativeComparisonOnComplex_singlePlus (M : X.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj M) n) :
    (comparisonOnComplex.{u+1} (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) (n : ℤ)).app
        ((DerivedPlus.singlePlusFunctor X.left.Modules).obj M)
        ((derivedSections.{u+1} (DerivedSections.relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
          ((DerivedPlus.singlePlusQIso X.left.Modules).hom.app M)
          (relativeSingleDerivedSectionsClass M n x)) =
      x.hom ≫ (singleComplexDerivedIso.{u+1} (toAbSheaf X.left) M).inv⟦(n : ℤ)⟧' := by
  exact comparisonOnComplex_singlePlus (toAbSheaf X.left)
    (DerivedSections.relativeGlobalSections X.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom)
    M (n : ℤ) (relativeSingleDerivedSectionsClass M n x) x.hom
    (relativeDerivedHomComparison_single M n x)

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
