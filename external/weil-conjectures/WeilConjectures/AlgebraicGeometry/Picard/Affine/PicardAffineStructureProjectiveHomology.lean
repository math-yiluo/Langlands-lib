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
import WeilConjectures.AlgebraicGeometry.Picard.Affine.PicardAffineProjectiveBaseChange
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Picard affine structure projective homology

## References

* Stacks Project, Tags 0BF2, 0B91, 08EB and 06Z0
* Stacks Project, Tags 0B91(2), 06Z0 and the structure-image argument in 0BF2
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A representing bounded projective model has the required universal low homology. -/
theorem picard_affine_structure_projective_homology
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf))
    (P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ)
    (hb : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)))
    (hp : (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)))
    (hrep : Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))) :
    (∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
        let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
        (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
          Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) := by
  classical
  intro B _ φ
  let g : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι ≫ k
  let p := pullback.snd f g
  let O := SheafOfModules.unit (pullback f g).ringCatSheaf
  let F := RingedSpace.moduleDirectImage p.toLRSHom.toShHom
  let Γ := moduleSpecΓFunctor (R := .of B)
  have : Γ.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have : HasInjectiveResolutions (pullback f g).Modules :=
    inferInstanceAs (HasInjectiveResolutions
      (SheafOfModules.{v} (moduleRings (pullback f g).toRingedSpace)))
  have hflat (n : ℤ) : Module.Flat (W.presheaf.obj (.op U)) (P.X n) := by
    let := hp n
    infer_instance
  have hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n) := by
    obtain ⟨a, b, hab⟩ := hb
    exact ⟨b, fun n hn ↦ hab n (Or.inr hn)⟩
  have hP := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat P hbounded hflat
  obtain ⟨eB⟩ := picard_affine_projective_base_change f M W k U hU htrivial P hP hrep B φ
  let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
  let T : ModuleCat.{v} B ⥤
      SheafOfModules.{v} (moduleRings (Spec (.of B)).toRingedSpace) := tilde.functor (.of B)
  have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : T.PreservesHomology := tilde_preservesHomology B
  let e (i : ℤ) : PB.homology i ≅
      Γ.obj ((schemeModuleHigherDirectImage p i).obj O) :=
    tilde.isoTop (R := .of B) (PB.homology i) ≪≫
      Γ.mapIso (((PB.sc i).mapHomologyIso T).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{v} (moduleRings (Spec (.of B)).toRingedSpace)) i).app
            ((T.mapHomologicalComplex (.up ℤ)).obj PB)).symm ≪≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (Spec (.of B)).toRingedSpace)) i).mapIso eB)
  constructor
  · intro i hi
    have hge := F.isGE_rightDerivedFunctor_obj_singleFunctor O
    have hz := (DerivedCategory.isGE_iff _ 0).mp hge i hi
    exact (Γ.map_isZero hz).of_iso (e i)
  · let z := F.homologyRightDerivedFunctorObjSingleFunctorIso O 0 ≪≫
      (Modules.pushforward p).rightDerivedZeroIsoSelf.app O
    let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
    let u := SheafOfModules.unit (Spec (.of B)).ringCatSheaf
    have : IsIso (Modules.tensorPullbackObjUnitToUnit p) :=
      (Modules.tensorPullbackObjUnitToUnit_isIso p).1
    let c := asIso (Modules.tensorPullbackObjUnitToUnit p)
    have hu : IsIso (adj.unit.app u) := hO g
    let d : u ≅ (Modules.pushforward p).obj O :=
      asIso (adj.unit.app u) ≪≫ (Modules.pushforward p).mapIso c
    let b : Γ.obj u ≅ ModuleCat.of B B :=
      Γ.mapIso (tildeSelf (R := .of B)).symm ≪≫
        ((tilde.toTildeΓNatIso (R := .of B)).app (ModuleCat.of B B)).symm
    exact ⟨(e 0) ≪≫ Γ.mapIso z ≪≫ Γ.mapIso d.symm ≪≫ b⟩

end AlgebraicGeometry.Scheme
