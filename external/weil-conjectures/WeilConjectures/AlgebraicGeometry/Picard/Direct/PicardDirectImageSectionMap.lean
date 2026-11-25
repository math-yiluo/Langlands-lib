/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDegreeZeroMateSquare
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-! # The fixed degree-zero section comparison

## References

* Stacks Project, Tags 08HY, 0B91 and 0D5S
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Apply degree-zero homology to a test morphism and the canonical base-change mate,
then the degree-zero direct-image comparison; evaluate on 1 and restrict to top.
All data are actual canonical maps. Only the inverse of the canonical structure-sheaf
comparison is used; its invertibility is already proved. -/
def picardDirectImageSectionMap {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W) :
    picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t →+
      Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let a : pullback f (t ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t ≫ k)) (pullback.snd f (t ≫ k) ≫ t)
      (by rw [Category.assoc]; exact pullback.condition)
  have ha : a ≫ pullback.fst f k = pullback.fst f (t ≫ k) := pullback.lift_fst ..
  have hb : a ≫ pullback.snd f k = pullback.snd f (t ≫ k) ≫ t := pullback.lift_snd ..
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k))))).symm
    (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
  let d : (Modules.pullback a).obj M ≅ N :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
  let B := schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (t ≫ k))
    t a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (schemeDerivedDirectImage (pullback.snd f (t ≫ k))).map
        (Modules.canonicalSinglePullbackMap a M ≫
          (DerivedCategory.singleFunctor _ 0).map d.hom)
  let U := SheafOfModules.unit (moduleRings W.toRingedSpace)
  have hU : SheafOfModules.IsInvertible.{v, v, v} U := by
    dsimp [U]
    exact SheafOfModules.instIsInvertibleUnit.{v, v, v}
  letI := hU
  have : IsIso (Modules.canonicalSinglePullbackMap t U) :=
    Modules.isIso_canonicalSinglePullbackMap t U
  let e := asIso (Modules.canonicalSinglePullbackMap t U) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit t.toRingCatSheafHom))
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let z := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).app
      (SheafOfModules.unit (moduleRings T.toRingedSpace))
  letI : IsGrothendieckAbelian.{v}
      (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI : EnoughInjectives (pullback f (t ≫ k)).Modules :=
    by
      change EnoughInjectives
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace))
      exact IsGrothendieckAbelian.enoughInjectives.{v, v, v + 1}
  letI : HasInjectiveResolutions (pullback f (t ≫ k)).Modules := inferInstance
  let r := Modules.canonicalDirectImageH0Iso (pullback.snd f (t ≫ k)) N
  let m := fun ξ ↦ z.inv ≫ H.map e.inv ≫ H.map ξ ≫ H.map B ≫ r.hom
  exact
    { toFun := fun ξ ↦ N.presheaf.map
        (homOfLE (pullback.snd f (t ≫ k)).preimage_top.ge).op
          ((m ξ).val.app (Opposite.op ⊤) (1 : Γ(T, ⊤)))
      map_zero' := by
        have hm : m 0 = 0 := by simp only [m, Functor.map_zero, comp_zero, zero_comp]
        rw [hm]
        change N.presheaf.map _ (0 : Γ(N, _)) = 0
        exact map_zero _
      map_add' := by intros; simp [m, Preadditive.comp_add, Preadditive.add_comp] }

end
end AlgebraicGeometry.Scheme
