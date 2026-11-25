/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition

/-! # Componentwise derived pullback square comparison

Source: Stacks Project, Tags 0D5S and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The pinned pullback-square comparison, with its component formula explicit.
The equality transport acts on objects, as in `schemeDerivedBaseChangeMap`.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-pc-t2-open-square-comparison). -/
noncomputable def singleComplexOpenSquareComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    derivedPullback g ⋙ derivedPullback f' ⟶ derivedPullback f ⋙ derivedPullback g' := by
  let c := @singleComplexOpenPinnedComposition.{u, w} _
  let q := (c f' g).hom ≫
    eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm) ≫ (c g' f).inv
  refine ⟨fun M ↦ (c f' g).hom.app M ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj M) h.symm) ≫
    (c g' f).inv.app M, ?_⟩
  intro M N t
  simpa only [q, NatTrans.comp_app, eqToHom_app] using q.naturality t

end AlgebraicGeometry
