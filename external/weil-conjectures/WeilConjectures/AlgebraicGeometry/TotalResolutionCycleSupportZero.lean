/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- A total cycle lying in column zero comes from a vertical cycle in that column.
Source: Stacks Project, Homology, Tag 09IZ, proof, final column-zero representative.
(blueprint: aux-total-resolution-cycle-support-zero)

Proof. Each component j.f is the injection of the column-zero summand into a
coproduct, and is therefore a split monomorphism. Write iCycles(z)=j.f(n)(x).
The chain-map equation for j and the fact that z is a cycle imply
j.f(n+1)(d(x))=0. Injectivity gives d(x)=0, so x defines a vertical cycle y.
The inclusion of y is x, which proves the equality. -/
theorem total_resolution_cycle_support_zero
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (j : K.X 0 ⟶ K.total (ComplexShape.up ℤ))
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (hj : ∀ q, j.f q = K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp))
    (z : (K.total (ComplexShape.up ℤ)).cycles n)
    (x : (K.X 0).X n)
    (hx : (K.total (ComplexShape.up ℤ)).iCycles n z = j.f n x) :
    ∃ y : (K.X 0).cycles n,
      (K.total (ComplexShape.up ℤ)).iCycles n z = j.f n ((K.X 0).iCycles n y) := by
  have hm : Mono (j.f (n + 1)) := by
    rw [hj]
    dsimp [HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    infer_instance
  have hz : (K.total (ComplexShape.up ℤ)).d n (n + 1)
      ((K.total (ComplexShape.up ℤ)).iCycles n z) = 0 := by
    exact congrArg (fun f => f z)
      ((K.total (ComplexShape.up ℤ)).iCycles_d n (n + 1))
  have hdx : (K.X 0).d n (n + 1) x = 0 := by
    apply (ModuleCat.mono_iff_injective (j.f (n + 1))).mp hm
    rw [map_zero]
    have hc := congrArg (fun f => f x) (j.comm n (n + 1)).symm
    change j.f (n + 1) ((K.X 0).d n (n + 1) x) =
      (K.total (ComplexShape.up ℤ)).d n (n + 1) (j.f n x) at hc
    rw [← hx] at hc
    exact hc.trans hz
  let y : (K.X 0).cycles n := ((K.X 0).sc n).cyclesMk x (by
    change ((K.X 0).d n ((ComplexShape.up ℤ).next n)).hom x = 0
    rw [CochainComplex.next]
    exact hdx)
  refine ⟨y, ?_⟩
  have hy : (K.X 0).iCycles n y = x :=
    ((K.X 0).sc n).i_cyclesMk x _
  rw [hy]
  exact hx

end WeilConjectures.DerivedTotalResolution
