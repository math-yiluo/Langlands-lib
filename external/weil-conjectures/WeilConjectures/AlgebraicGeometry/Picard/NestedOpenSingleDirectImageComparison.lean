/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Nested open restriction of a single direct image
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Nested open restriction of a single direct image. -/
theorem nestedOpen_single_directImage_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (V : U.toScheme.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  letI := dV
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace))
  Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
      ((schemeOpenRestriction S U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
    (@Functor.mapDerivedCategory _ _ _ dV _ _ _ _
      (Scheme.Modules.overEquiv V).inverse _ _ _).obj
      ((schemeDerivedDirectImage (pullback.snd f (V.ι ≫ U.ι))).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F)))) := by
  classical
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := dV
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace))
  let a := pullback.fst f (V.ι ≫ U.ι)
  let r := pullback.snd f (V.ι ≫ U.ι)
  let : HasDerivedCategory.{wX} X.Modules := inferInstanceAs
    (HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{wS} S.Modules := inferInstanceAs
    (HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace)))
  let : HasDerivedCategory.{u + 1} (pullback f (V.ι ≫ U.ι)).Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace)))
  let : HasDerivedCategory.{u + 1} V.toScheme.Modules := dV
  let : Abelian.HasKInjectiveResolutions X.Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : Abelian.HasKInjectiveResolutions (pullback f (V.ι ≫ U.ι)).Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace)))
  let : Abelian.HasKInjectiveResolutions V.toScheme.Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)))
  let A := Scheme.Modules.restrictFunctor a
  let B := Scheme.Modules.restrictFunctor (V.ι ≫ U.ι)
  let b := SheafOfModules.overFunctor.{u} (moduleRings U.toScheme.toRingedSpace) V
  let E := (Scheme.Modules.overEquiv V).inverse
  let R := schemeOpenRestriction S U ⋙ b
  let : A.Additive := inferInstance
  let : B.Additive := inferInstance
  let : PreservesFiniteLimits A := (openImmersion_restriction_derived_properties a).1
  let : A.PreservesKInjectiveComplexes := (openImmersion_restriction_derived_properties a).2
  let : PreservesFiniteLimits B := (openImmersion_restriction_derived_properties (V.ι ≫ U.ι)).1
  let : b.Additive := Functor.additive_of_preserves_binary_products _
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  let : R.Additive := inferInstance
  let : PreservesFiniteLimits R := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits R := comp_preservesFiniteColimits _ _
  have h : R ⋙ (Scheme.Modules.overEquiv V).functor ≅ B :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv V) ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) _ ≪≫
      (Scheme.Modules.restrictFunctorComp V.ι U.ι).symm
  have hR : R ≅ B ⋙ E :=
    (Functor.rightUnitor R).symm ≪≫
      Functor.isoWhiskerLeft R (Scheme.Modules.overEquiv V).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h E
  have hbase := Scheme.Modules.pushforwardRestrictIso
    (IsPullback.of_hasPullback f (V.ι ≫ U.ι))
  have h0 : Scheme.Modules.pushforward f ⋙ R ≅
      A ⋙ (Scheme.Modules.pushforward r ⋙ E) :=
    Functor.isoWhiskerLeft _ hR ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hbase E ≪≫ Functor.associator _ _ _
  let : (Scheme.Modules.pushforward f).Additive :=
    RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  let : (Scheme.Modules.pushforward r).Additive :=
    RingedSpace.moduleDirectImage_additive r.toLRSHom.toShHom
  have hD : schemeDerivedDirectImage f ⋙ R.mapDerivedCategory ≅
      (@Functor.mapDerivedCategory _ _ _
        (inferInstance : HasDerivedCategory.{wX} X.Modules) _ _ _
        (inferInstance : HasDerivedCategory.{u + 1} (pullback f (V.ι ≫ U.ι)).Modules) A _ _ _) ⋙
        (schemeDerivedDirectImage r ⋙ E.mapDerivedCategory) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{wX, wS, wS} _ R).symm ≪≫
      Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, wX, wS} h0 ≪≫
      Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1,
        wX, u + 1, wS} A _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{u + 1, u + 1, wS} _ E) ≪≫
      Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{wX, u + 1} A) _
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  let hcoeff := (Scheme.Modules.restrictAdjunction a).leftAdjointUniq adj
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F
  exact ⟨(Functor.mapDerivedCategoryCompIso (schemeOpenRestriction S U) b).app
      ((schemeDerivedDirectImage f).obj K) ≪≫ hD.app K ≪≫
    (schemeDerivedDirectImage r ⋙ E.mapDerivedCategory).mapIso
      ((A.mapDerivedCategorySingleFunctor 0).app F ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (hcoeff.app F))⟩

end
end AlgebraicGeometry
