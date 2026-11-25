/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def matchingBoundaryShape (n : ℕ) : MulticospanShape where
  L := Fin (n + 3)
  R := {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2}
  fst p := p.val.1
  snd p := p.val.2

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def matchingBoundaryIndex {C : Type u} [Category.{v} C] (K : SimplicialObject C) (n : ℕ) :
    MulticospanIndex (matchingBoundaryShape n) C where
  left _ := K _⦋n + 1⦌
  right _ := K _⦋n⦌
  fst p := K.δ (p.val.2.pred (Fin.ne_zero_of_lt p.property))
  snd p := K.δ (p.val.1.castLT (Nat.lt_of_lt_of_le p.property
    (Nat.le_of_lt_succ p.val.2.isLt)))

end CategoryTheory.SimplicialObject
