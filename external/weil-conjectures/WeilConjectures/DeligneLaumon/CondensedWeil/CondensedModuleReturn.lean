/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # The specified module return before geometric evaluation

This construction separates the actual pullback compositors and return equation
from the later scalar evaluation. It chooses no data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

/-- The semilinear module return from the specified compositors and return equation.
Source: latest blueprint, second proof paragraph of theorem-pure-lisse-sheaves-over-relative;
the local Frobenius operator uses precisely these maps before scalar evaluation
(blueprint: def-zl-condensed-module-return). -/
@[irreducible] def moduleReturnMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S X : Scheme.{u}} (a : X ⟶ X) (s : S ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (θ : (CondensedRing.upperStar Λ a).obj M ⟶ M) (z : S ⟶ X)
    (h : z ≫ a = s ≫ z) :
    (CondensedRing.upperStar Λ s).obj ((CondensedRing.upperStar Λ z).obj M) ⟶
      (CondensedRing.upperStar Λ z).obj M :=
  (CondensedRing.upperStarComp Λ s z).inv.app M ≫
    eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) h.symm) ≫
      (CondensedRing.upperStarComp Λ z a).hom.app M ≫
        (CondensedRing.upperStar Λ z).map θ

/-- Apply a specified point insertion, then evaluate a semilinear return.
Source: latest blueprint local Frobenius convention; insertion precedes the
geometric evaluation of the module return
(blueprint: def-zl-condensed-module-return). -/
@[irreducible] def evaluateModuleReturn
    {C E : Type*} [Category C] [Category E] (F : C ⥤ E) (T : C ⥤ C)
    (ι : F ⟶ T ⋙ F) (M : C) (r : T.obj M ⟶ M) : End (F.obj M) :=
  .of (ι.app M ≫ F.map r)

end WeilConjectures.CondensedWeil
