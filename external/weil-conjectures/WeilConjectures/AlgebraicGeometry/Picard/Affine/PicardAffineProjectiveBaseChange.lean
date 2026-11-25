/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift

import WeilConjectures.AlgebraicGeometry.Picard.Affine.PicardAffineStructureModelTransport
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.Flat.FlatInvertibleCanonicalDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Base change for an affine K-flat direct-image model

## References

* Stacks Project, Tags 0A1D, 08DW(2) and 06Z0
* Stacks Project, Tags 0A1D, 08DW(2), 08FE and 06Z0
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem structurePullbackIso
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T Y : Scheme.{v}} (a : T ⟶ Y) :
    Nonempty ((derivedPullback a).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          (SheafOfModules.unit T.ringCatSheaf)) := by
  have := Modules.isIso_canonicalSinglePullbackMap a
    (SheafOfModules.unit Y.ringCatSheaf)
  let t := (Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)
  have := (Modules.tensorPullbackObjUnitToUnit_isIso a).1
  exact ⟨asIso (Modules.canonicalSinglePullbackMap a _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((t.app _).symm ≪≫ asIso (Modules.tensorPullbackObjUnitToUnit a))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem structureImageBaseChange
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S T T' : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [QuasiCompact f] [IsSeparated f]
    (j : T ⟶ S) (a : T' ⟶ T) :
    Nonempty ((derivedPullback a).obj
        ((schemeDerivedDirectImage (pullback.snd f j)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f j).toRingedSpace)) 0).obj
              (SheafOfModules.unit (pullback f j).ringCatSheaf))) ≅
      (schemeDerivedDirectImage (pullback.snd f (a ≫ j))).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f (a ≫ j)).toRingedSpace)) 0).obj
            (SheafOfModules.unit (pullback f (a ≫ j)).ringCatSheaf))) := by
  let q : pullback f (a ≫ j) ⟶ pullback f j :=
    pullback.lift (pullback.fst f (a ≫ j)) (pullback.snd f (a ≫ j) ≫ a)
      (by simp only [Category.assoc, pullback.condition])
  have sq : IsPullback q (pullback.snd f (a ≫ j)) (pullback.snd f j) a := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f j)
      (h₂₂ := j) (v₁₃ := f) ?_ ?_ (IsPullback.of_hasPullback f j)
    · simpa only [q, pullback.lift_fst] using IsPullback.of_hasPullback f (a ≫ j)
    · exact pullback.lift_snd _ _ _
  have hbc := Modules.isIso_derivedBaseChange_of_flat_invertible
    (pullback.snd f j) a q (pullback.snd f (a ≫ j)) sq
    (SheafOfModules.unit (pullback f j).ringCatSheaf)
  obtain ⟨e⟩ := structurePullbackIso q
  exact ⟨asIso (schemeDerivedBaseChangeMap (pullback.snd f j)
      (pullback.snd f (a ≫ j)) a q sq.w
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (pullback f j).ringCatSheaf))) ≪≫
    (schemeDerivedDirectImage (pullback.snd f (a ≫ j))).mapIso e⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
/-- Sheafified scalar extension of an affine K-flat model represents the structure
sheaf's derived direct image after base change to the spectrum of the new ring. -/
theorem picard_affine_projective_base_change
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [QuasiCompact f] [IsSeparated f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf))
    (P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      L.Acyclic → (CochainComplex.mapBifunctor L P
        (MonoidalCategory.curriedTensor _)).Acyclic)
    (hrep : Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))) :
    ∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
      let g : Spec (.of B) ⟶ S :=
        Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι ≫ k
      Nonempty
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{v} B ⥤
              SheafOfModules.{v} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{v} (moduleRings (pullback f g).toRingedSpace)) 0).obj
                (SheafOfModules.unit (pullback f g).ringCatSheaf))) := by
  intro B _ φ
  let R := W.presheaf.obj (.op U)
  let j : Spec R ⟶ S := hU.isoSpec.inv ≫ U.ι ≫ k
  let a : Spec (.of B) ⟶ Spec R := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨erep⟩ := picard_affine_structure_model_transport f M W k U hU htrivial P hrep
  have hPk : (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor N P (MonoidalCategory.curriedTensor _))).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (BraidedCategory.braiding _ _) hr, hr⟩
  obtain ⟨α⟩ := derivedPullback_tilde_kFlat_natIso R B φ
  obtain ⟨ebc⟩ := structureImageBaseChange f j a
  exact ⟨(α.app ⟨P, hPk⟩).symm ≪≫ (derivedPullback a).mapIso erep ≪≫ ebc⟩

end AlgebraicGeometry.Scheme
