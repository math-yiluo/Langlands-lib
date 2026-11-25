/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-! # Pullback of an invertible condensed Weil structure along its specified square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

/-- Apply the coefficient inverse image and its specified Frobenius-square comparison.
Source: latest blueprint, restriction to open and closed constant-field components
in the second proof paragraph of theorem-pure-lisse-sheaves-over-relative
(blueprint: def-zl-condensed-weil-pullback-object). -/
@[irreducible] def pullbackWeilObject
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} {a : U ⟶ U} {b : X ⟶ X} {j : U ⟶ X}
    (sq : CommSq a j j b)
    (M : Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ b)) :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ a) :=
  (Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison Λ sq).symm).obj M

/-- Any property of the carrier and structure of the specified pullback may be
read using the explicit inverse-image carrier and comparison-composed structure.
Source: the projection equations of the actual inverse-image algebra construction
(blueprint: def-zl-condensed-weil-pullback-object). -/
theorem pullbackWeilObject_property
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} {a : U ⟶ U} {b : X ⟶ X} {j : U ⟶ X}
    (sq : CommSq a j j b)
    (M : Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ b))
    (Q : ∀ N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
      ((CondensedRing.upperStar Λ a).obj N ≅ N) → Prop)
    (h : Q (pullbackWeilObject Λ sq M).carrier (pullbackWeilObject Λ sq M).str) :
    Q ((CondensedRing.upperStar Λ j).obj M.carrier)
      ((CondensedRing.upperStarSquareComparison Λ sq).symm.app M.carrier ≪≫
        (CondensedRing.upperStar Λ j).mapIso M.str) := by
  unfold pullbackWeilObject at h
  simpa only [Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier,
    Endofunctor.IsoAlgebra.mapOfNatIso_obj_str] using h

end WeilConjectures.CondensedWeil
