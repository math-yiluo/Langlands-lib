/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.Matrix.Block
/-! # Split coordinate sequence underlying a Weil flag

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-coordinate-splitting).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.CondensedWeilPointFlags
/-- The standard inclusion I and projection P, with their coordinate retraction R and
section S, satisfy RI=1, PS=1, PI=0, and IR+SP=1. This includes n=0.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-coordinate-splitting).

Proof: each product is a sum of products of Kronecker entries. The first product is
the identity on the first n coordinates, the second the identity on the last coordinate,
and the third is zero because an initial coordinate is never the last. For the final
identity, divide its row and column into initial and final coordinates: the first
summand is the initial-coordinate identity, and the second the final-coordinate identity. -/
theorem coordinate_split_equations {K : Type u} [Field K] (n : ℕ) :
    let I : Matrix (Fin (n+1)) (Fin n) K := fun r k ↦ if r = k.castSucc then 1 else 0
    let R : Matrix (Fin n) (Fin (n+1)) K := I.transpose
    let P : Matrix (Fin 1) (Fin (n+1)) K :=
      fun _ k ↦ if k = Fin.last n then 1 else 0
    let S : Matrix (Fin (n+1)) (Fin 1) K := P.transpose
    R * I = 1 ∧ P * S = 1 ∧ P * I = 0 ∧ I * R + S * P = 1 := by
  classical
  dsimp only
  constructor
  · ext r k
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.castSucc_inj, eq_comm]
  constructor
  · ext r k
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Subsingleton.elim r k]
  constructor
  · ext r k
    simp [Matrix.mul_apply, Fin.castSucc_ne_last]
  · ext r k
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    refine Fin.lastCases ?_ (fun r ↦ ?_) r
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · simp [(fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
      · simp [Fin.castSucc_ne_last,
          (fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · simp [Fin.castSucc_ne_last,
          (fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, Fin.castSucc_inj]
end WeilConjectures.CondensedWeilPointFlags
