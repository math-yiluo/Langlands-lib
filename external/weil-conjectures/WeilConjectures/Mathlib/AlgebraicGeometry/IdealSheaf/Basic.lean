/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The ideal of sections on an affine open disjoint from the support

On an affine open disjoint from the support of a quasi-coherent ideal, the ideal of
sections is the unit ideal.

We also record `AlgebraicGeometry.Scheme.IdealSheafData.le_ker_iff_range_subset_support`:
an ideal sheaf is contained in the kernel of a morphism from a reduced scheme if and only
if the range of the morphism lies in its support; and
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_sup`, the set-level form of
`support_sup`, and `AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal`: the kernel of a morphism
from a reduced scheme is the vanishing ideal of the closure of its range.

Finally we record the monotonicity of the product of ideal sheaves, its distributivity over
suprema and the containment of the support of a power in the support.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On an affine open disjoint from the support, the ideal is the unit ideal.
(blueprint: `lemma:nagata-ideal-unit-off-support`) -/
lemma ideal_eq_top_of_disjoint_support {U : X.affineOpens}
    (hU : Disjoint (U.1 : Set X) (I.support : Set X)) : I.ideal U = ⊤ := by
  have hsub : X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 ⊆ (∅ : Set X) := fun x hx ↦
    (Set.disjoint_left.mp hU hx.2 (I.zeroLocus_inter_subset_supportSet U hx)).elim
  have h := (U.2.fromSpec_image_zeroLocus _).trans_subset hsub
  simp only [Set.subset_empty_iff, Set.image_eq_empty] at h
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h

/-- An ideal sheaf is contained in the kernel of a morphism from a reduced scheme exactly
when the range of the morphism lies in its support. -/
lemma le_ker_iff_range_subset_support {W : Scheme.{u}} (g : W ⟶ X) [IsReduced W] :
    I ≤ g.ker ↔ Set.range g ⊆ (I.support : Set X) := by
  rw [← map_bot, le_map_iff_comap_le, le_bot_iff, ← support_eq_top_iff, support_comap]
  simp [TopologicalSpace.Closeds.ext_iff, Set.preimage_eq_univ_iff]

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
range: both are the largest ideal sheaf whose support contains the range. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal {W : Scheme.{u}} (g : W ⟶ X)
    [IsReduced W] : g.ker = vanishingIdeal ⟨closure (Set.range g), isClosed_closure⟩ := by
  refine le_antisymm ?_ ?_
  · rw [← le_support_iff_le_vanishingIdeal]
    exact closure_minimal ((le_ker_iff_range_subset_support _ g).mp le_rfl)
      (support _).isClosed
  · rw [le_ker_iff_range_subset_support]
    have : (⟨closure (Set.range g), isClosed_closure⟩ : TopologicalSpace.Closeds X) ≤
        (vanishingIdeal ⟨closure (Set.range g), isClosed_closure⟩).support :=
      le_support_iff_le_vanishingIdeal.mpr le_rfl
    exact subset_closure.trans this

/-- The support of a sum of ideal sheaves is the intersection of the supports: the
set-level form of `support_sup`. -/
lemma coe_support_sup (I₁ I₂ : X.IdealSheafData) :
    ((I₁ ⊔ I₂).support : Set X) = (I₁.support : Set X) ∩ (I₂.support : Set X) := by
  rw [support_sup, TopologicalSpace.Closeds.coe_inf]

/-- The product of quasi-coherent ideal sheaves is monotone in both arguments. -/
lemma mul_mono {I₁ I₂ J₁ J₂ : X.IdealSheafData} (hI : I₁ ≤ I₂) (hJ : J₁ ≤ J₂) :
    I₁ * J₁ ≤ I₂ * J₂ :=
  fun U ↦ Ideal.mul_mono (hI U) (hJ U)

/-- The product of quasi-coherent ideal sheaves distributes over suprema. -/
lemma iSup_mul {ι : Type*} (I : ι → X.IdealSheafData) (J : X.IdealSheafData) :
    (⨆ i, I i) * J = ⨆ i, I i * J :=
  Scheme.IdealSheafData.ext <| funext fun U ↦ by
    simp only [ideal_mul, Pi.mul_apply, ideal_iSup, iSup_apply, Submodule.iSup_mul]

/-- The support of a power of a quasi-coherent ideal sheaf is contained in its support. -/
lemma support_pow_le {I : X.IdealSheafData} (n : ℕ) : (I ^ n).support ≤ I.support := by
  cases n with
  | zero => simp
  | succ n => simp

end AlgebraicGeometry.Scheme.IdealSheafData
