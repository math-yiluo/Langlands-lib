/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Bounded-above flat module complexes are K-flat

Source: Stacks Project, More on Algebra, Lemma 15.59.1 (Tag 064K)
(blueprint: lem-pc-module-bounded-flat-kflat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-module-bounded-flat-kflat) Stacks Project, More on Algebra,
Lemma 15.59.1 (Tag 064K): a bounded-above cochain complex of flat modules over a
commutative ring is K-flat. Concretely, tensoring it with every acyclic complex
and taking the total complex gives an acyclic complex.

Proof: Translate termwise module flatness to categorical flatness with
`ModuleCat.flat_iff_flat`. Exact filtered colimits and the closed tensor structure
of modules let `kFlat_of_isStrictlyLE_of_flat` apply. Pass to the homotopy category;
`kFlat_iff_preserves_acyclic` gives acyclicity of tensoring an arbitrary acyclic
complex with `P`, and the quotient acyclicity equivalence returns the claim. -/
theorem acyclic_mapBifunctor_of_boundedAbove_flat
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) :
    ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic := by
  obtain ⟨b, hb⟩ := hbounded
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hb
  have (X : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight X))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have hP := kFlat_of_isStrictlyLE_of_flat P b
    (fun i ↦ (ModuleCat.flat_iff_flat (P.X i)).2 (hflat i))
  rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hP
  intro L hL
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hP
    ((HomotopyCategory.quotient _ _).obj L)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL)
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
  exact h.2

end CochainComplex
