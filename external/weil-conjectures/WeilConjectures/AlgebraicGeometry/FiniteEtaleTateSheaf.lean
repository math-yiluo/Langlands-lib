/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-!
# Signed finite Tate sheaves

Source: Stacks Project, Etale Cohomology, Tag 03PK, and signed tensor powers and duals
(auxiliary; not a blueprint node).

The nonnegative twists are the published `finiteEtaleTateTwist`. Only the extension to
negative integers by internal sheaf Hom is new here.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Extend the existing nonnegative finite Tate twists by sheaf duality. Source: Stacks
Project, Tag 03PK, finite Tate powers, and Modules on Sites, Tag 04TT, internal Hom
(auxiliary; not a blueprint node). -/
noncomputable def finiteEtaleTateSheaf (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (T : Scheme.{u}) (hA : (m : A) = 0) :
    ℤ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  | .ofNat n => finiteEtaleTateTwist T m A hA n
  | .negSucc n =>
      (ihom (finiteEtaleTateTwist T m A hA (n + 1))).obj
        (finiteEtaleTateTwist T m A hA 0)

/-- The local pure tensor in the published coefficient root line. The module enhancement
of roots of unity has the same underlying group, so its section `z` requires no choice.
Source: Stacks Project, Tags 03PK and 03EK, scalar extension generators
(auxiliary; not a blueprint node). -/
noncomputable def finiteEtaleTateOneGenerator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (T : Scheme.{u}) (hA : (m : A) = 0) (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) :
    (finiteEtaleTateSheaf A m T hA 1).obj.obj W :=
  (toSheafify T.smallEtaleTopology
    (finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))).app W
        (a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z)

end AlgebraicGeometry.Scheme
