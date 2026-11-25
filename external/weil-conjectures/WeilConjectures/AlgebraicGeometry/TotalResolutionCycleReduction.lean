/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleFiniteSupport
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleSupportStep
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleSupportZero

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Finite-support reduction for the left half-plane total complex.
Source: Stacks Project, Homology, Tag 09IZ, proof, finite-support induction.
(blueprint: lem-pc-derived-total-resolution-column-zero-cycle-reduction)

Proof. Put A_i = K.X (-i). For the given cycle z in degree n, let
x = iCycles(z), an element of the kernel of the total differential. The coproduct of
modules is a direct sum, so x has finite support in the columns. Positive
columns of K are zero. Thus x has components x_i in A_i^(n+i), for
0 ≤ i ≤ r, for some natural number r. If r > 0, the component of d x in
column r says that x_r is a vertical cycle. The component in column r-1
says that its horizontal image is a vertical boundary (with the total
complex sign). Exactness of the horizontal homology row at A_r lifts the
class of x_r to a class in A_(r+1)^(n+r). Choose a vertical cycle y
representing this class. It has total degree n-1 and vertical differential
zero. Subtract its total boundary, adjusting by the horizontal unit sign
if necessary: the component in column r becomes a vertical boundary.
Choose a primitive t in A_r^(n+r-1). Subtract the total boundary of the
appropriately signed t. The column-r component now vanishes, and the
only other component created lies in column r-1. The largest occupied
index decreases, so induction gives a homologous total cycle supported
in column zero. Its column-zero component is a cycle y of A_0, since its
vertical differential is zero. The specified components of j identify
its inclusion with j. The sum b of the signed correction terms has
degree n-1 and satisfies iCycles(z) = j(iCycles(y)) + d(b).
The zero class and the case r = 0 require no reduction. No boundedness
of the vertical complexes is used. -/
theorem total_resolution_column_zero_cycle_reduction
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (j : K.X 0 ⟶ K.total (ComplexShape.up ℤ))
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (hj : ∀ q, j.f q = K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp))
    (h_homology : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom) :
    ∀ z : (K.total (ComplexShape.up ℤ)).cycles n,
      ∃ y : (K.X 0).cycles n, ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          j.f n ((K.X 0).iCycles n y) +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
  have hind : ∀ r : ℕ, ∀ z : (K.total (ComplexShape.up ℤ)).cycles n,
      (∃ x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          Finset.sum (Finset.range (r + 1)) (fun i =>
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i))) →
      ∃ y : (K.X 0).cycles n, ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          j.f n ((K.X 0).iCycles n y) +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
    intro r
    induction r with
    | zero =>
        rintro z ⟨x, hx⟩
        let a : (K.X 0).X n :=
          (K.XXIsoOfEq _ _ _ (by simp : -(0 : ℤ) = 0) (add_zero n)).hom (x 0)
        have he := congrArg (fun f => f (x 0))
          (K.XXIsoOfEq_hom_ιTotal (ComplexShape.up ℤ)
            (by simp : -(0 : ℤ) = 0) (add_zero n) n (by simp))
        change K.ιTotal (ComplexShape.up ℤ) 0 n n (by simp) a =
          K.ιTotal (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (by simp) (x 0) at he
        have ha : (K.total (ComplexShape.up ℤ)).iCycles n z = j.f n a := by
          rw [hj, he]
          simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton] at hx
          change (K.total (ComplexShape.up ℤ)).iCycles n z =
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (x 0) at hx
          rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (by simp)] at hx
          exact hx
        obtain ⟨y, hy⟩ := total_resolution_cycle_support_zero K j n hj z a ha
        exact ⟨y, 0, by simpa using hy⟩
    | succ r ih =>
        rintro z ⟨x, hx⟩
        obtain ⟨z', x', b, hx', hb⟩ :=
          total_resolution_cycle_support_step K n h_homology r z x hx
        obtain ⟨y, b', hy⟩ := ih z' ⟨x', hx'⟩
        refine ⟨y, b' + b, ?_⟩
        rw [hb, hy, map_add, add_assoc]
  intro z
  obtain ⟨r, x, hx⟩ := total_resolution_element_finite_support K n h_positive
    ((K.total (ComplexShape.up ℤ)).iCycles n z)
  exact hind r z ⟨x, hx⟩

end WeilConjectures.DerivedTotalResolution
