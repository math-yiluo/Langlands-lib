/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingDerivedScalarExtension.RingDerivedScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option linter.privateModule false

/-! # Perfect scalar transport along a ring isomorphism
Source: HRS Proposition 4.3(3); Stacks Project Tag 06Y6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe r wA wB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingDerivedScalarExtension

private theorem perfect_of_iso {R : Type r} [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{r} R)]
    {K L : DerivedCategory (ModuleCat.{r} R)}
    (h : DerivedCategory.IsPerfectRingComplex K) (e : K ≅ L) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ i⟩⟩

end CategoryTheory.RingDerivedScalarExtension
