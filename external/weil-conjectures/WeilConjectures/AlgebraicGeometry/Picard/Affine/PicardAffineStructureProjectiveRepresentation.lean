/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatSingleDerivedDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties

/-! # Picard affine structure projective representation

## References

* Stacks Project, Tag 08FE, and the tensor pullback composition and unit comparisons
* Stacks Project, Tags 0BF2 (perfect-image paragraph), 0B91(2), 08EB and 06Z0
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit affine-site equivalence underlying affinePerfectSheafification. -/
private noncomputable def affineTransportEquivalence (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    SheafOfModules.{v} (moduleRings (Spec (W.presheaf.obj (.op U))).toRingedSpace) ≌
      SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) :=
  let F := Modules.restrictFunctor hU.isoSpec.hom
  let G := Modules.restrictFunctor hU.isoSpec.inv
  let e : SheafOfModules.{v}
      (moduleRings (Spec (W.presheaf.obj (.op U))).toRingedSpace) ≌ U.toScheme.Modules :=
    CategoryTheory.Equivalence.mk F G
      ((Modules.restrictFunctorId).symm ≪≫
        Modules.restrictFunctorCongr (by simp) ≪≫
        Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
      ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
        Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  e.trans (Modules.overEquiv U).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Deriving the open square involves several independently chosen localization instances.
/-- Open base change and a coefficient trivialization, before using any perfectness. -/
private theorem open_trivialized_image_spectrum_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    let T := (affineTransportEquivalence W U hU).functor
    letI : T.Additive := Functor.additive_of_preserves_binary_products T
    Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
      T.mapDerivedCategory.obj
        ((schemeDerivedDirectImage
          (pullback.snd f ((hU.isoSpec.inv ≫ U.ι) ≫ k))).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{v}
            (moduleRings (pullback f ((hU.isoSpec.inv ≫ U.ι) ≫ k)).toRingedSpace)) 0).obj
            (SheafOfModules.unit
              (pullback f ((hU.isoSpec.inv ≫ U.ι) ≫ k)).ringCatSheaf)))) := by
  classical
  let j := hU.isoSpec.inv ≫ U.ι
  let Y := pullback f (j ≫ k)
  let r := pullback.snd f (j ≫ k)
  let p := pullback.snd f k
  let q : Y ⟶ pullback f k :=
    pullback.lift (pullback.fst f (j ≫ k)) (r ≫ j)
      (by simp [r, Category.assoc, pullback.condition])
  have hqfst : q ≫ pullback.fst f k = pullback.fst f (j ≫ k) := by simp [q]
  have hsq : IsPullback q r p j := by
    apply IsPullback.of_right _ (by simp [q]) (IsPullback.of_hasPullback f k)
    simpa only [hqfst] using IsPullback.of_hasPullback f (j ≫ k)
  have : IsOpenImmersion q :=
    MorphismProperty.of_isPullback hsq.flip (inferInstance : IsOpenImmersion j)
  let : HasDerivedCategory.{v + 1} (pullback f k).Modules := inferInstanceAs
    (HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)))
  let : HasDerivedCategory.{v + 1} W.Modules := inferInstanceAs
    (HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings W.toRingedSpace)))
  let : HasDerivedCategory.{v + 1} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{v + 1} (Spec (W.presheaf.obj (.op U))).Modules := inferInstanceAs
    (HasDerivedCategory.{v + 1} (SheafOfModules.{v}
      (moduleRings (Spec (W.presheaf.obj (.op U))).toRingedSpace)))
  let : Abelian.HasKInjectiveResolutions (pullback f k).Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)))
  let : Abelian.HasKInjectiveResolutions Y.Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions (SheafOfModules.{v} (moduleRings Y.toRingedSpace)))
  let A := Modules.restrictFunctor q
  let B := Modules.restrictFunctor j
  have : A.Additive := (inferInstance : A.Additive)
  have : A.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties q).2
  have : PreservesFiniteLimits A := (openImmersion_restriction_derived_properties q).1
  have : PreservesFiniteLimits B := (openImmersion_restriction_derived_properties j).1
  let e := affineTransportEquivalence W U hU
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let T := e.functor
  let H := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U ⋙ e.inverse
  let L := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have : H.Additive := inferInstance
  have hHB : H ≅ B :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) _ ≪≫
      (Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm
  have hbase := Modules.pushforwardRestrictIso hsq
  have h0 : Modules.pushforward p ⋙ H ≅ A ⋙ Modules.pushforward r :=
    Functor.isoWhiskerLeft _ hHB ≪≫ hbase
  have : (Modules.pushforward p).Additive :=
    RingedSpace.moduleDirectImage_additive p.toLRSHom.toShHom
  have : (Modules.pushforward r).Additive :=
    RingedSpace.moduleDirectImage_additive r.toLRSHom.toShHom
  have hD : schemeDerivedDirectImage p ⋙ H.mapDerivedCategory ≅
      A.mapDerivedCategory ⋙ schemeDerivedDirectImage r :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{v + 1, v + 1, v + 1}
      _ H).symm ≪≫
      Functor.rightDerivedFunctorNatIso.{v, v, v + 1, v + 1, v + 1, v + 1} h0 ≪≫
      Functor.rightDerivedFunctorCompIso.{v, v, v, v + 1, v + 1, v + 1,
        v + 1, v + 1, v + 1} A _ ≪≫
      Functor.isoWhiskerRight
        (Functor.rightDerivedFunctorIsoMapDerivedCategory.{v + 1, v + 1} A) _
  let t : Y ⟶ pullback f (U.ι ≫ k) :=
    pullback.lift (pullback.fst f (j ≫ k)) (r ≫ hU.isoSpec.inv)
      (by simp [r, j, Category.assoc, pullback.condition])
  obtain ⟨htr⟩ := htrivial
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction q
  have hu := (Modules.tensorPullbackObjUnitToUnit_isIso t).1
  let coeff : A.obj ((Modules.tensorPullback (pullback.fst f k)).obj M) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    ((Modules.restrictAdjunction q).leftAdjointUniq adj).app _ ≪≫
      ((Modules.tensorPullbackCompositionIso q (pullback.fst f k)
        (pullback.fst f (j ≫ k)) hqfst).app M).symm ≪≫
      (Modules.tensorPullbackCompositionIso t (pullback.fst f (U.ι ≫ k))
        (pullback.fst f (j ≫ k)) (by simp [t])).app M ≪≫
      (Modules.tensorPullback t).mapIso htr ≪≫ asIso (Modules.tensorPullbackObjUnitToUnit t)
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
      ((Modules.tensorPullback (pullback.fst f k)).obj M)
  let c : (H.mapDerivedCategory.obj ((schemeDerivedDirectImage p).obj K)) ≅
      (schemeDerivedDirectImage r).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit Y.ringCatSheaf)) :=
    hD.app K ≪≫ (schemeDerivedDirectImage r).mapIso
      ((A.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso coeff)
  let hc : H ⋙ T ≅ L :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L e.counitIso ≪≫
      Functor.rightUnitor L
  let hcD : H.mapDerivedCategory ⋙ T.mapDerivedCategory ≅ L.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso H T ≪≫ Functor.mapDerivedCategoryNatIso hc
  exact ⟨(hcD.app ((schemeDerivedDirectImage p).obj K)).symm ≪≫
    T.mapDerivedCategory.mapIso c⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A bounded finite-projective model of the restricted trivialized coefficient image. -/
theorem picard_affine_structure_projective_representation
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let R := W.presheaf.obj (.op U)
  let j := hU.isoSpec.inv ≫ U.ι
  let Y := pullback f (j ≫ k)
  let p := pullback.snd f (j ≫ k)
  let O := SheafOfModules.unit Y.ringCatSheaf
  have : SheafOfModules.IsInvertible.{v, v, v} O := by
    dsimp [O]
    exact SheafOfModules.instIsInvertibleUnit.{v, v, v}
  have : O.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation O
  let D := (schemeDerivedDirectImage p).obj
    ((DerivedCategory.singleFunctor (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj O)
  have hD : IsPerfect (Spec R) D :=
    properFlat_single_derivedDirectImage_perfect p O (Modules.isFlatOver_of_isInvertible p O)
  let E : schemeDerivedQCohCategory (Spec R) :=
    ⟨D, schemeDerivedQCohProperty_of_isPerfect (Spec R) D hD⟩
  obtain ⟨P, hb, hf, hp, ⟨hP⟩⟩ :=
    (perfect_iff_affine_bounded_projective R E).mp hD
  let T := (affineTransportEquivalence W U hU).functor
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨c⟩ := open_trivialized_image_spectrum_comparison f M W k U hU htrivial
  refine ⟨P, hb, hf, hp, ⟨c ≪≫ T.mapDerivedCategory.mapIso hP ≪≫ ?_⟩⟩
  exact T.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (tilde.functor R ⋙ T)) (.up ℤ)).app P)

end

end AlgebraicGeometry.Scheme
