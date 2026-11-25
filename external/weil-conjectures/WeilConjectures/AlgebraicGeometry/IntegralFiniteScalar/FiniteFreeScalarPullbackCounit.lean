/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import all WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaConstruction
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement

/-! # Scalar pullback mate and representative counits
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm

private instance map_monoid {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] betaTotalNatIso betaOrdinary betaTargetIso
  betaRestrictedCounit betaScalarCounit

-- Compare the normalized derived mate with its ordinary unit square.
/-- The normalized scalar-pullback mate commutes with the exact representative factors
and the derived-to-ordinary scalar counits, on every cochain complex. -/
theorem finiteFreeScalar_pullback_scalarCounit
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    (scalarSixChange a X).map
        ((CondensedRing.upperStar Λ.X f).mapDerivedCategoryFactors.hom.app C) ≫
      scalarCounit a X
        (((CondensedRing.upperStar Λ.X f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).hom
          (.up ℤ)).app C) =
    (D.theta a f).hom.app (DerivedCategory.Q.obj C) ≫
      (scalarSixPull Λ' f).map (scalarCounit a Y C) ≫
      (CondensedRing.upperStar Λ'.X f).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
            (.up ℤ)).obj C) := by
  let F := CondensedRing.upperStar Λ.X f
  let G := CondensedRing.upperStar Λ'.X f
  let EX := Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (betaMap a X)
  let EY := Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (betaMap a Y)
  let RX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (betaMap a X)
  let RY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (betaMap a Y)
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let EC := (EY.mapHomologicalComplex (.up ℤ)).obj C
  let p := (NatTrans.mapHomologicalComplex
    (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).hom (.up ℤ)).app C
  let q := (NatTrans.mapHomologicalComplex
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
  let ηX := ((Mod.extendRestrictAdjunction (betaMap a X)).mapHomologicalComplex
    (.up ℤ)).unit.app FC
  let ηY := ((Mod.extendRestrictAdjunction (betaMap a Y)).mapHomologicalComplex
    (.up ℤ)).unit.app C
  have hOrd : (F.mapHomologicalComplex (.up ℤ)).map ηY ≫ q =
      ηX ≫ (RX.mapHomologicalComplex (.up ℤ)).map p := by
    ext n : 1
    exact ordinaryScalarUnit (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f (C.X n)
  have hOrd' := naturalOrdinaryFac F.mapDerivedCategoryFactors.hom ηY ηX
    ((RX.mapHomologicalComplex (.up ℤ)).map p) q hOrd
  have hq := Functor.exactSquare_fac
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm EC
  rw [Functor.square_symm_hom] at hq
  have ho := RX.mapDerivedCategoryFactors.hom.naturality p
  dsimp only [Functor.comp_map] at ho
  have h := mateModel
    (Mod.derivedExtendMapDerivedCategoryAdjunction (betaMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (betaMap a Y))
    F.mapDerivedCategory G.mapDerivedCategory
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv
    (F.mapDerivedCategoryFactors.hom.app C) ((betaScalarCounit a X).app FC)
    (DerivedCategory.Q.map p) ((betaScalarCounit a Y).app C)
    (G.mapDerivedCategoryFactors.hom.app EC)
    (RX.mapDerivedCategoryFactors.hom.app _)
    (RX.mapDerivedCategoryFactors.hom.app _)
    (RY.mapDerivedCategoryFactors.hom.app EC)
    (F.mapDerivedCategoryFactors.hom.app _ ) (DerivedCategory.Q.map q)
    (DerivedCategory.Q.map ηX) (DerivedCategory.Q.map ηY)
    (DerivedCategory.Q.map ((RX.mapHomologicalComplex (.up ℤ)).map p))
    (by simpa only [betaScalarCounit, betaScalarCounit_eq, RX, RY, FC, F, ηX, ηY,
        Functor.comp_obj] using
      Mod.KFlatScalarTower.computationCounit_unit (betaMap a X) FC)
    (by simpa only [betaScalarCounit, betaScalarCounit_eq, RX, RY, FC, F, ηX, ηY,
        Functor.comp_obj] using
      Mod.KFlatScalarTower.computationCounit_unit (betaMap a Y) C)
    ho hq hOrd'
  rw [D.thetaNormalization]
  simpa only [scalarSixChange, scalarSixAdjunctionLeft, scalarSixPull, scalarSixPullHom,
    Adjunction.pushHomOfComapIso, betaScalarCounit] using h

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
