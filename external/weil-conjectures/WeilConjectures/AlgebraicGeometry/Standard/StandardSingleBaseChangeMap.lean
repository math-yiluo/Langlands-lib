/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
public import Mathlib.AlgebraicGeometry.Fiber

/-! # Canonical comparison for a module in degree zero

Source: Stacks Project, Tag 08HY, Remark base-change, and Tag 0A1D,
lemma-base-change-tensor (blueprint: def-pc-standard-single-base-change-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical base-change map followed by direct image of the single-complex
pullback counit. This is a construction for every module and every base morphism;
it asserts neither monicity nor epicity.
Source: Stacks Project, Tag 08HY and Tag 0A1D.
(blueprint: def-pc-standard-single-base-change-map). -/
noncomputable def standardSingleBaseChangeMap
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) ⟶
    (schemeDerivedDirectImage (pullback.snd p g)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M)) :=
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  schemeDerivedBaseChangeMap p (pullback.snd p g) g (pullback.fst p g)
    pullback.condition ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
    (schemeDerivedDirectImage (pullback.snd p g)).map
      (Scheme.picardTermwiseSingleMap (pullback.fst p g) M)

end AlgebraicGeometry
