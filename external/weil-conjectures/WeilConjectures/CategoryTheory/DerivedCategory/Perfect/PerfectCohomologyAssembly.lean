/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingTriangleClosure

set_option linter.privateModule false

/-!
# Perfectness from bounded perfect cohomology

Source: Stacks Project, More on Algebra, Tag 066U, lemma-cohomology-perfect
(blueprint: lem-sf-perfect-cohomology-assembly).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CategoryTheory.Pretriangulated

namespace DerivedCategory

private lemma perfect_of_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K L : DerivedCategory (ModuleCat.{u} A)} (h : IsPerfectRingComplex K)
    (e : K ≅ L) : IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ eP⟩⟩

private lemma perfect_shift {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K : DerivedCategory (ModuleCat.{u} A)} (h : IsPerfectRingComplex K) (n : ℤ) :
    IsPerfectRingComplex (K⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  refine ⟨P⟦n⟧, a - n, b - n, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun i ↦ hP (i + n)
  · exact ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩

end DerivedCategory
