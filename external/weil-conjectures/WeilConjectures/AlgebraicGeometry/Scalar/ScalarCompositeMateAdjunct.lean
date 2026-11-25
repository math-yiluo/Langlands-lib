/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition

/-! # The adjunct of the transported scalar composite mate

The direct-image compositors are the universal right-derived comparisons computed
on K-injective resolutions. The scalar/pullback comparisons are transported from
left derived pullback to the exact termwise inverse image. The inverse composite
Hom equivalence is precisely the two-counit formula for Adj_B.

## References

* Stacks Project, Tag 0E46, with the normalized comparisons of Tags 07A7, 0D6D and 0D6E
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem transported_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P : C ⥤ D} {R : D ⥤ C} {P' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : P ⊣ R) (b : P' ⊣ R')
    {E : C ⥤ D} {E' : C' ⥤ D'} (e : P ≅ E) (e' : P' ≅ E')
    (Q : C ⥤ C') (T : D ⥤ D') (l : Q ⋙ P' ⟶ P ⋙ T)
    (M : D) (m : Q.obj (R.obj M) ⟶ R'.obj (T.obj M))
    (hm : P'.map m ≫ b.counit.app _ = l.app _ ≫ T.map (a.counit.app M)) :
    E'.map m ≫ (b.ofNatIsoLeft e').counit.app _ =
      (e'.inv.app _ ≫ l.app _ ≫ T.map (e.hom.app _)) ≫
        T.map ((a.ofNatIsoLeft e).counit.app M) := by
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [e'.inv.naturality_assoc, hm]
  simp only [← T.map_comp, Iso.hom_inv_id_app_assoc]

private theorem compositor_counit
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (s : Y ⟶ Z) (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) (r ≫ s)).mapDerivedCategory.map
        ((Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
          (lowerStarComp (ModuleCat.{u + 1} A) r s)).hom.app M) ≫
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r ≫ s)).counit.app M =
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) r s) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
        (R(lowerStar (ModuleCat.{u + 1} A) s).obj
          (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) ≫
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).comp
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)).counit.app M := by
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r ≫ s)) _ _
    (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp
      (ModuleCat.{u + 1} A) r s)).symm]
  exact conjugateEquiv_counit _ _ _ M

private theorem composite_mate_calculation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P Pc : C ⥤ D} {R Rc : D ⥤ C}
    {P' Pc' : C' ⥤ D'} {R' Rc' : D' ⥤ C'}
    (a : P ⊣ R) (ac : Pc ⊣ Rc) (b : P' ⊣ R') (bc : Pc' ⊣ Rc')
    (c : Pc ≅ P) (c' : Pc' ≅ P') (k : R ≅ Rc) (k' : R' ≅ Rc')
    (Q : C ⥤ C') (T : D ⥤ D')
    (l : Q ⋙ Pc' ⟶ Pc ⋙ T) (L : Q ⋙ P' ⟶ P ⋙ T) (M : D)
    (m : Q.obj (Rc.obj M) ⟶ Rc'.obj (T.obj M))
    (ha : Pc.map (k.hom.app M) ≫ ac.counit.app M =
      c.hom.app (R.obj M) ≫ a.counit.app M)
    (hb : Pc'.map (k'.hom.app (T.obj M)) ≫ bc.counit.app (T.obj M) =
      c'.hom.app (R'.obj (T.obj M)) ≫ b.counit.app (T.obj M))
    (hm : Pc'.map m ≫ bc.counit.app _ = l.app _ ≫ T.map (ac.counit.app M))
    (hl : c'.hom.app (Q.obj (R.obj M)) ≫ L.app (R.obj M) =
      l.app (R.obj M) ≫ T.map (c.hom.app (R.obj M))) :
    (b.homEquiv _ _).symm (Q.map (k.hom.app M) ≫ m ≫ k'.inv.app (T.obj M)) =
      L.app (R.obj M) ≫ T.map (a.counit.app M) := by
  have hb' : Pc'.map (k'.inv.app (T.obj M)) ≫
      c'.hom.app (R'.obj (T.obj M)) ≫ b.counit.app (T.obj M) =
      bc.counit.app (T.obj M) := by
    rw [← hb, ← Pc'.map_comp_assoc, Iso.inv_hom_id_app, Pc'.map_id, Category.id_comp]
  apply (cancel_epi (c'.hom.app (Q.obj (R.obj M)))).1
  rw [Adjunction.homEquiv_counit, ← c'.hom.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hb', hm]
  have hn := l.naturality (k.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← T.map_comp, ha, T.map_comp, ← reassoc_of% hl]

/-- The transported composite scalar mate has the prescribed two-counit adjunct. -/
theorem scalarMate_comp_homEquiv_symm
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X) :
    (((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s).comp
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)).homEquiv
      ((scalarExtension φ Z).obj
        (R(lowerStar (ModuleCat.{u + 1} A) s).obj
          (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)))
      ((scalarExtension φ X).obj M)).symm
        ((scalarExtension φ Z).map
            ((Functor.rightDerivedFunctorCompIso'
              (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
              (lowerStarComp (ModuleCat.{u + 1} A) r s)).hom.app M) ≫
          (scalarMate φ (r ≫ s)).app M ≫
          (Functor.rightDerivedFunctorCompIso'
            (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
            (lowerStarComp (ModuleCat.{u + 1} B) r s)).inv.app
              ((scalarExtension φ X).obj M)) =
      (upperStar (ModuleCat.{u + 1} B) r).mapDerivedCategory.map
          ((Functor.isoWhiskerLeft _
              (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) s).symm ≪≫
            scalarPullbackIso φ s ≪≫ Functor.isoWhiskerRight
              (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) s) _).hom.app
                (R(lowerStar (ModuleCat.{u + 1} A) s).obj
                  (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (Functor.isoWhiskerLeft _
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) r).symm ≪≫
          scalarPullbackIso φ r ≪≫ Functor.isoWhiskerRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r) _).hom.app
              ((upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategory.obj
                (R(lowerStar (ModuleCat.{u + 1} A) s).obj
                  (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (scalarExtension φ X).map
          ((upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory.map
            ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).counit.app
              (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (scalarExtension φ X).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app M) := by
  let a := ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r))
  let b := ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r))
  let ac := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r ≫ s)
  let bc := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (r ≫ s)
  let cA := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} A) r s) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let cB := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) r s) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let kA := Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
    (lowerStarComp (ModuleCat.{u + 1} A) r s)
  let kB := Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
    (lowerStarComp (ModuleCat.{u + 1} B) r s)
  let l := fun {W T : Scheme.{u}} (f : W ⟶ T) ↦
    (Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm ≪≫
    scalarPullbackIso φ f ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _).hom
  let L : scalarExtension φ Z ⋙
      ((upperStar (ModuleCat.{u + 1} B) s).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} B) r).mapDerivedCategory) ⟶
      ((upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory) ⋙ scalarExtension φ X :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (l s) _ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (l r) ≫ (Functor.associator _ _ _).inv
  have hm : (upperStar (ModuleCat.{u + 1} B) (r ≫ s)).mapDerivedCategory.map
        ((scalarMate φ (r ≫ s)).app M) ≫ bc.counit.app _ =
      (l (r ≫ s)).app _ ≫ (scalarExtension φ X).map (ac.counit.app M) := by
    rw [show ac = (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) (r ≫ s)).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (r ≫ s)) from
        mapDerivedUpperStarLowerStarAdjunction_eq _ _,
      show bc = (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} B) (r ≫ s)).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (r ≫ s)) from
        mapDerivedUpperStarLowerStarAdjunction_eq _ _]
    simpa only [l, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom] using transported_counit
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r ≫ s))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (r ≫ s))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (r ≫ s))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (r ≫ s))
        (scalarExtension φ Z) (scalarExtension φ X) (scalarPullbackIso φ (r ≫ s)).hom
        M ((scalarMate φ (r ≫ s)).app M)
        (mateEquiv_counit _ _ (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ (r ≫ s)).hom) M)
  have hl : cB.hom.app ((scalarExtension φ Z).obj (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
      L.app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) =
      (l (r ≫ s)).app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) ≫
        (scalarExtension φ X).map (cA.hom.app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) := by
    simpa only [L, l, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      scalarPullback_composition φ s r (r ≫ s) rfl (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))
  have h := composite_mate_calculation a ac b bc cA cB kA kB
    (scalarExtension φ Z) (scalarExtension φ X) (l (r ≫ s)) L M
    ((scalarMate φ (r ≫ s)).app M)
    (compositor_counit A r s M)
    (compositor_counit B r s ((scalarExtension φ X).obj M)) hm hl
  simpa only [a, b, kA, kB, L, l, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Adjunction.comp_counit_app,
    Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.Etale
