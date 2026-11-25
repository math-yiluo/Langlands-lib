/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryAbelianSquare
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryEdges
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinarySquareCoherence

/-! # The ordinary coefficient-normalized component square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {T : Type u₄} [Category.{v₄} T] [MonoidalCategory T]
  (F : C ⥤ D) (G : D ⥤ T) (H : C ⥤ E) (I : E ⥤ T)
  [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [I.LaxMonoidal]
  {A : C} [MonObj A] {B : D} [MonObj B] {R : E} [MonObj R] {S : T} [MonObj S]
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
