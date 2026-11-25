/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

/-!
# Boundaries lie in filtered-complex cycles

Source: Stacks Project, Homology, Tag 012K, the displayed inclusions between B and Z.
(blueprint: lem-sp-filtered-complex-boundaries-le-cycles).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem image_le_pullback {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (h : f ≫ g = 0) (S : Subobject A) (T : Subobject D) :
    (Subobject.«exists» f).obj S ≤ (Subobject.pullback g).obj T := by
  apply leOfHom
  refine ((Subobject.existsPullbackAdj f).homEquiv _ _).symm ?_
  apply homOfLE
  apply Subobject.le_of_factors
  apply (pullback_factors_iff f _ _).mpr
  apply (pullback_factors_iff g _ _).mpr
  simpa only [Category.assoc, h, comp_zero] using
    (Subobject.factors_zero : T.Factors (0 : (S : C) ⟶ D))

/-- Boundaries lie in cycles, even before requiring a positive page.
Source: Stacks Project, Tag 012K, the displayed inclusions between B and Z.
(blueprint: lem-sp-filtered-complex-boundaries-le-cycles).

Proof. The image of the incoming differential is contained in the inverse image
of every filtration step under the outgoing differential, since d squared is zero.
Intersect with F^p, add F^(p+1), pull back to F^p, and take the graded image.
All these operations preserve the containment. -/
theorem filteredComplex_boundaries_le_cycles (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (p n r : ℤ) :
    F.complexBoundaries p n r ≤ F.complexCycles p n r := by
  unfold DecreasingFiltration.complexBoundaries DecreasingFiltration.complexCycles
  apply leOfHom
  apply (Subobject.«exists» _).map
  apply homOfLE
  apply leOfHom
  apply (Subobject.pullback _).map
  apply homOfLE
  apply sup_le_sup_right
  apply inf_le_inf_left
  exact image_le_pullback _ _ (K.d_comp_d _ _ _ ) _ _

end CategoryTheory
