/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-! # Data and component equation for a tensor scalar tower -/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false

universe u v
namespace CategoryTheory

/-- The category structures, functors and normalized comparisons of one tensor tower.
This record keeps changes of category presentation outside the component equation.
Source: the tensor clause of the coefficient-tower argument.
(blueprint: def-weil-tensor-tower-datum). -/
structure TensorTowerDatum (C D E : Type u) where
  [catC : Category.{v} C]
  [catD : Category.{v} D]
  [catE : Category.{v} E]
  U : C × C ⥤ C
  V : D × D ⥤ D
  B : E × E ⥤ E
  F : C ⥤ D
  G : D ⥤ E
  H : C ⥤ E
  a : F ⋙ G ≅ H
  p : U ⋙ F ≅ F.prod F ⋙ V
  q : V ⋙ G ≅ G.prod G ⋙ B
  r : U ⋙ H ≅ H.prod H ⋙ B

namespace TensorTowerDatum
variable {C D E : Type u}

/-- The actual component equality, with all its category data held in a single record.
Source: the tensor clause of scalarOperationsOrdinary_tower.
(blueprint: def-weil-tensor-tower-datum). -/
@[irreducible] def Coherent (d : TensorTowerDatum.{u, v} C D E) : Prop :=
  letI := d.catC
  letI := d.catD
  letI := d.catE
  ∀ X Y : C,
    d.G.map (d.p.hom.app (X, Y)) ≫ d.q.hom.app (d.F.obj X, d.F.obj Y) ≫
      d.B.map (Prod.mkHom (d.a.hom.app X) (d.a.hom.app Y)) =
    d.a.hom.app (d.U.obj (X, Y)) ≫ d.r.hom.app (X, Y)

end TensorTowerDatum
end CategoryTheory
