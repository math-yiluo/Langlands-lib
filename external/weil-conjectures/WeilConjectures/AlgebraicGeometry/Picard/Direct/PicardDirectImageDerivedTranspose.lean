/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageUnitMorphism

/-! # The derived transpose before structure-sheaf normalization

## References

* Stacks Project, Tags 08HY and 0D5S
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

/-- Normalize the test morphism's source on T, apply canonical base change and
its coefficient comparison, then transpose under the pinned derived adjunction.
The source remains the derived pullback of the structure sheaf on T; no fibre
structure-sheaf comparison is applied. -/
@[irreducible]
def picardDirectImageDerivedTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (derivedPullback (pullback.snd f (t ≫ k))).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings T.toRingedSpace))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L) := by
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
  let p := pullback.snd f (t ≫ k)
  let adj := Classical.choose (exists_schemeDerivedAdjunction p
    (hAdd := (Classical.choose exists_derivedPullbackComposition) p)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) p)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) p))
  exact (adj.homEquiv _ _).symm (e.inv ≫ ξ ≫ B)

end
end AlgebraicGeometry.Scheme
