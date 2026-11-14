import Langlands.Geometry.Building.Kottwitz.ReductiveMap

/-! # Restriction of the actual cocenter quotient to a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k G) (c : Cocenter k G)

/-- The actual cocenter quotient restricted to a chosen maximal torus. -/
def cocenterTorusRestriction : a.torus ⟶ c.torus :=
  Additive.ofMul (a.inclusion ≫ c.quotient)

end Langlands.Geometry.Building.Kottwitz
