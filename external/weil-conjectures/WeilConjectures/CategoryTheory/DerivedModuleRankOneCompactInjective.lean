/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject

@[expose] public section

universe w vH
namespace CategoryTheory
open Limits DirectSum

open Classical in
/-- Injectivity of the rank-one comparison map.

Proof in words: for each index i, the coproduct universal property gives a projection p_i
which is the identity on summand i and zero on every other summand. Composing the comparison
of a finitely supported family with p_i recovers its i-th coordinate, as direct-sum induction
shows. Equal comparison images therefore have equal coordinates and are equal. This argument
works for any source in a preadditive category, including the empty family and the zero ring.
Source: the coproduct universal property; Stacks Project, Tag 0F5X, first paragraph, for the
rank-one compactness application.
(auxiliary; not a blueprint node)
-/
theorem derivedModule_rankOne_comparison_injective
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (I : Type (max w vH))
    (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :
    let _ := Classical.decEq I
    let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))
    Function.Injective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp P (Sigma.ι E i)) :
        (⨁ i : I, (P ⟶ E i)) →+ (P ⟶ ∐ E)) := by
  classical
  dsimp
  let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
    (ModuleCat.of S (ULift.{vH} S))
  let c := DirectSum.toAddMonoid (fun i : I ↦ Preadditive.rightComp P (Sigma.ι E i))
  let p (i : I) : ∐ E ⟶ E i :=
    Sigma.desc (fun j ↦ if h : j = i then eqToHom (congrArg E h) else 0)
  have hc (x : ⨁ i : I, (P ⟶ E i)) (i : I) : c x ≫ p i = x i := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j f =>
      by_cases h : j = i
      · subst j
        simp [c, p, Preadditive.rightComp]
      · simp [c, p, Preadditive.rightComp, Category.assoc,
          DirectSum.of_eq_of_ne, h, Ne.symm h]
    | add x y hx hy => simp [map_add, Preadditive.add_comp, hx, hy]
  intro x y hxy
  apply DirectSum.ext
  intro i
  rw [← hc x i, ← hc y i, hxy]

end CategoryTheory
