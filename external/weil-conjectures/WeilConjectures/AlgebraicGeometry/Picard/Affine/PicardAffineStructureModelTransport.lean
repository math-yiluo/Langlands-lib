/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Transport of a localized affine structure-image model

## References

* Stacks Project, Tags 08FE and 06Z0
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance derivedModules
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{v}) : HasDerivedCategory.{v + 1} Y.Modules :=
  inferInstanceAs (HasDerivedCategory.{v + 1}
    (SheafOfModules.{v} (moduleRings Y.toRingedSpace)))

private instance moduleKInjectives (Y : Scheme.{v}) :
    Abelian.HasKInjectiveResolutions Y.Modules :=
  inferInstanceAs (Abelian.HasKInjectiveResolutions
    (SheafOfModules.{v} (moduleRings Y.toRingedSpace)))

private theorem open_single_image
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {Y W T Z : Scheme.{v}} (p : Y ⟶ W) (j : T ⟶ W) [IsOpenImmersion j]
    (r : Z ⟶ Y) (p' : Z ⟶ T) (sq : IsPullback r p' p j) (N : Y.Modules) :
    Nonempty ((Modules.restrictFunctor j).mapDerivedCategory.obj
        ((schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj N)) ≅
      (schemeDerivedDirectImage p').obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Z.toRingedSpace)) 0).obj
          ((Modules.tensorPullback r).obj N))) := by
  have : IsOpenImmersion r :=
    MorphismProperty.of_isPullback sq.flip (P := @IsOpenImmersion) inferInstance
  let A := Modules.restrictFunctor r
  let B := Modules.restrictFunctor j
  have : PreservesFiniteLimits A := (openImmersion_restriction_derived_properties r).1
  have : A.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties r).2
  have : PreservesFiniteLimits B := (openImmersion_restriction_derived_properties j).1
  have hbase := Modules.pushforwardRestrictIso sq
  have : (RingedSpace.moduleDirectImage p.toLRSHom.toShHom).Additive :=
    RingedSpace.moduleDirectImage_additive p.toLRSHom.toShHom
  have : (RingedSpace.moduleDirectImage p'.toLRSHom.toShHom).Additive :=
    RingedSpace.moduleDirectImage_additive p'.toLRSHom.toShHom
  have : (Modules.pushforward p).Additive :=
    RingedSpace.moduleDirectImage_additive p.toLRSHom.toShHom
  have : (Modules.pushforward p').Additive :=
    RingedSpace.moduleDirectImage_additive p'.toLRSHom.toShHom
  let δ : schemeDerivedDirectImage p ⋙ B.mapDerivedCategory ≅
      A.mapDerivedCategory ⋙ schemeDerivedDirectImage p' :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ B).symm ≪≫
      Functor.rightDerivedFunctorNatIso hbase ≪≫
      Functor.rightDerivedFunctorCompIso A _ ≪≫
      Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory A) _
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction r
  let coeff := (Modules.restrictAdjunction r).leftAdjointUniq adj
  exact ⟨δ.app _ ≪≫ (schemeDerivedDirectImage p').mapIso
    ((A.mapDerivedCategorySingleFunctor 0).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (coeff.app N))⟩

/-- Transport the localized representation to the spectrum of the affine coordinate ring. -/
theorem picard_affine_structure_model_transport
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf))
    (P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ)
    (hrep : Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))) :
    let j : Spec (W.presheaf.obj (.op U)) ⟶ S := hU.isoSpec.inv ≫ U.ι ≫ k
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{v} (W.presheaf.obj (.op U)) ⥤
            SheafOfModules.{v}
              (moduleRings (Spec (W.presheaf.obj (.op U))).toRingedSpace))
            (tilde.functor (W.presheaf.obj (.op U))))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P) ≅
        (schemeDerivedDirectImage (pullback.snd f j)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f j).toRingedSpace)) 0).obj
              (SheafOfModules.unit (pullback f j).ringCatSheaf))) := by
  classical
  let R := W.presheaf.obj (.op U)
  let j₀ : Spec R ⟶ W := hU.isoSpec.inv ≫ U.ι
  let j : Spec R ⟶ S := hU.isoSpec.inv ≫ U.ι ≫ k
  let q : pullback f j ⟶ pullback f k :=
    pullback.lift (pullback.fst f j) (pullback.snd f j ≫ j₀)
      (by simpa only [j, j₀, Category.assoc] using pullback.condition (f := f) (g := j))
  have sq : IsPullback q (pullback.snd f j) (pullback.snd f k) j₀ := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f k)
      (h₂₂ := k) (v₁₃ := f) ?_ ?_ (IsPullback.of_hasPullback f k)
    · simpa only [q, pullback.lift_fst, j, j₀, Category.assoc] using
        IsPullback.of_hasPullback f j
    · exact pullback.lift_snd _ _ _
  let t : pullback f j ⟶ pullback f (U.ι ≫ k) :=
    pullback.lift (pullback.fst f j) (pullback.snd f j ≫ hU.isoSpec.inv)
      (by simpa only [j, Category.assoc] using pullback.condition (f := f) (g := j))
  obtain ⟨triv⟩ := htrivial
  have := (Modules.tensorPullbackObjUnitToUnit_isIso t).1
  let eM : (Modules.tensorPullback (pullback.fst f j)).obj M ≅
      SheafOfModules.unit (pullback f j).ringCatSheaf :=
    (Modules.tensorPullbackCompositionIso t (pullback.fst f (U.ι ≫ k))
      (pullback.fst f j) (pullback.lift_fst _ _ _)).app M ≪≫
    (Modules.tensorPullback t).mapIso triv ≪≫ asIso (Modules.tensorPullbackObjUnitToUnit t)
  let N := (Modules.tensorPullback (pullback.fst f k)).obj M
  let ecoeff : (Modules.tensorPullback q).obj N ≅
      SheafOfModules.unit (pullback f j).ringCatSheaf :=
    ((Modules.tensorPullbackCompositionIso q (pullback.fst f k)
      (pullback.fst f j) (pullback.lift_fst _ _ _)).app M).symm ≪≫ eM
  obtain ⟨ebase⟩ := open_single_image (pullback.snd f k) j₀ q (pullback.snd f j) sq N
  let O := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U
  let E := (Modules.overEquiv U).functor
  let F := Modules.restrictFunctor hU.isoSpec.inv
  let H := E ⋙ F
  let B := Modules.restrictFunctor j₀
  have : B.Additive := inferInstance
  have : PreservesFiniteColimits B := by dsimp [B]; infer_instance
  have : PreservesFiniteLimits B := (openImmersion_restriction_derived_properties j₀).1
  have : (affinePerfectSheafification W U hU).Additive := by
    unfold affinePerfectSheafification
    infer_instance
  have : H.Additive := inferInstance
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteColimits H := inferInstance
  let θ : O ⋙ H ≅ B :=
    (Functor.associator O E F).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) F ≪≫
      (Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm
  obtain ⟨rep⟩ := hrep
  let K := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj N)
  let K' := ((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P
  let erep : B.mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K') :=
    ((Functor.mapDerivedCategoryNatIso θ).app K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso O H).symm.app K ≪≫
      H.mapDerivedCategory.mapIso rep ≪≫ H.mapDerivedCategoryFactors.app K'
  let T : ModuleCat.{v} R ⥤
      SheafOfModules.{v} (moduleRings (Spec R).toRingedSpace) := tilde.functor R
  have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : T.Additive := inferInstanceAs (tilde.functor R).Additive
  let δ : affinePerfectSheafification W U hU ⋙ H ≅ T := by
    let A := Modules.restrictFunctor hU.isoSpec.hom
    let E' := (Modules.overEquiv U).inverse
    change (T ⋙ A ⋙ E') ⋙ (E ⋙ F) ≅ T
    exact Functor.associator T (A ⋙ E') (E ⋙ F) ≪≫
      Functor.isoWhiskerLeft T
        ((Functor.associator A E' (E ⋙ F)).symm ≪≫
          Functor.isoWhiskerRight
            (Functor.associator A E' E ≪≫
              Functor.isoWhiskerLeft A (Modules.overEquiv U).counitIso ≪≫
              Functor.rightUnitor A) F ≪≫
          (Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
          Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫ Modules.restrictFunctorId) ≪≫
      Functor.rightUnitor T
  let ecomplex : ((H.mapHomologicalComplex (.up ℤ)).obj K') ≅
      (T.mapHomologicalComplex (.up ℤ)).obj P :=
    ((Functor.mapHomologicalComplexCompIso δ (.up ℤ)).app P)
  exact ⟨(DerivedCategory.Q.mapIso ecomplex).symm ≪≫ erep.symm ≪≫ ebase ≪≫
    (schemeDerivedDirectImage (pullback.snd f j)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso ecoeff)⟩

end AlgebraicGeometry.Scheme
