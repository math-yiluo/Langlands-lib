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
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleReduction
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Column-zero representatives in a total complex

Source: Stacks Project, Homology, Tag 09IZ, proof, finite-support induction.
(blueprint: lem-pc-derived-total-resolution-column-zero)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Exact horizontal homology rows allow every total homology class to be
represented in column zero.
Source: Stacks Project, Homology, Tag 09IZ, proof, second paragraph.
(blueprint: lem-pc-derived-total-resolution-column-zero)

Proof. Put A_i = K.X (-i). Represent a total homology class in degree n by
an element x of the kernel of the total differential. The coproduct of
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
in column zero. Its column-zero component is a cycle of A_0, since its
vertical differential is zero. The specified components of j identify
its inclusion with j, so this cycle's homology class is a preimage.
The zero class and the case r = 0 require no reduction. No boundedness
of the vertical complexes is used. -/
theorem total_resolution_column_zero_surjective
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (j : K.X 0 ⟶ K.total (ComplexShape.up ℤ))
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (hj : ∀ q : ℤ, j.f q = K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp))
    (h_homology : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom) :
    Function.Surjective (HomologicalComplex.homologyMap j n).hom := by
  let A := K.X 0
  let B := K.total (ComplexShape.up ℤ)
  have hred := total_resolution_column_zero_cycle_reduction K j n h_positive hj h_homology
  intro x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ n)).mp inferInstance x
  obtain ⟨y, b, hb⟩ := hred z
  have hz : z = HomologicalComplex.cyclesMap j n y + B.toCycles (n - 1) n b := by
    apply (ModuleCat.mono_iff_injective (B.iCycles n)).mp inferInstance
    rw [map_add]
    have hj := congr($(HomologicalComplex.cyclesMap_i j n) y)
    have hd := congr($(B.toCycles_i (n - 1) n) b)
    change B.iCycles n (HomologicalComplex.cyclesMap j n y) =
      j.f n (A.iCycles n y) at hj
    change B.iCycles n (B.toCycles (n - 1) n b) = B.d (n - 1) n b at hd
    rw [hj, hd]
    exact hb
  refine ⟨A.homologyπ n y, ?_⟩
  have hn := congr($(HomologicalComplex.homologyπ_naturality j n) y)
  change HomologicalComplex.homologyMap j n (A.homologyπ n y) =
    B.homologyπ n (HomologicalComplex.cyclesMap j n y) at hn
  have hb0 := congr($(B.toCycles_comp_homologyπ (n - 1) n) b)
  change B.homologyπ n (B.toCycles (n - 1) n b) = 0 at hb0
  rw [hn, hz, map_add, hb0, add_zero]

end WeilConjectures.DerivedTotalResolution
