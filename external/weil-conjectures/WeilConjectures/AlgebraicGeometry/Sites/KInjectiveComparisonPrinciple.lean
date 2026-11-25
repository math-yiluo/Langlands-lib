/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The comparison principle for a K-injective target
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex.IsKInjective

/-- Precomposition by a quasi-isomorphism induces a bijection on homotopy classes of maps
into a K-injective complex, in any abelian category admitting the derived category. -/
theorem precomp_bijective_of_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : CochainComplex C ℤ} (s : A ⟶ B) [QuasiIso s]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj B ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I ↦
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s ≫ g) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let f := DerivedCategory.Qh.map (q.map s)
  have hf : IsIso f := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map s)
    rw [NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C)]
    infer_instance
  constructor
  · intro g h e
    apply (Qh_map_bijective (q.obj B) I).injective
    apply (cancel_epi f).mp
    simpa only [f, ← Functor.map_comp] using congrArg DerivedCategory.Qh.map e
  · intro g
    obtain ⟨h, hh⟩ := (Qh_map_bijective (q.obj B) I).surjective
      (inv f ≫ DerivedCategory.Qh.map g)
    refine ⟨h, (Qh_map_bijective (q.obj A) I).injective ?_⟩
    rw [Functor.map_comp, hh]
    change f ≫ inv f ≫ DerivedCategory.Qh.map g = _
    simp

end CochainComplex.IsKInjective
