/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Data.Int.Interval

/-! # Finite diagonals of a bounded-below bicomplex

Source: Stacks Project, Homology, Tag 012Z
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

private theorem hasCoproduct_of_finite_nonzero
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type}
    (X : D → C) (P : D → Prop) [Finite {i // P i}]
    (h : ∀ i, ¬ P i → IsZero (X i)) : HasCoproduct X := by
  classical
  let Y := fun i : {i // P i} ↦ X i.val
  let c : Cofan X := Cofan.mk (∐ Y)
    (fun i ↦ if hi : P i then Sigma.ι Y ⟨i, hi⟩ else 0)
  refine ⟨⟨c, Cofan.IsColimit.mk _
    (fun s ↦ Sigma.desc (f := Y) (fun i : {i // P i} ↦ s.inj i.val)) ?_ ?_⟩⟩
  · intro s i
    by_cases hi : P i
    · simp [c, hi]
    · exact (h i hi).eq_of_src _ _
  · intro s m hm
    apply Sigma.hom_ext (f := Y)
    intro i
    simpa [c, i.property] using hm i.val

/-- A common lower bound in the first degree and nonnegative second degree give a total.
Source: Stacks Project, Homology, Tag 012Z
(auxiliary; not a blueprint node).

Proof: in total degree n, the potentially nonzero summands have a ≤ p ≤ n
and q = n-p. This is a finite set, even when a is negative or n < a.
Form its finite coproduct, put zero inclusion maps on all omitted summands,
and extend the coproduct universal property using their zero-object property.
These coproducts give `HasTotal` degree by degree. -/
theorem hasTotal_of_boundedBelow
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (a : ℤ) (hbelow : ∀ p q : ℤ, p < a → IsZero ((K.X p).X q))
    (hneg : ∀ p q : ℤ, q < 0 → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  classical
  intro n
  let D := (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)) ⁻¹' {n}
  let P := fun i : D ↦ a ≤ i.val.1 ∧ 0 ≤ i.val.2
  have hsum (i : D) : i.val.1 + i.val.2 = n := by
    exact i.property
  let f : {i // P i} → ↥(Finset.Icc a n) := fun i ↦
    ⟨i.val.val.1, Finset.mem_Icc.mpr ⟨i.property.1, by
      have hs := hsum i.val
      have hn := i.property.2
      omega⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hij
    · have hp : i.val.val.1 = j.val.val.1 := congrArg Subtype.val hij
      have hi := hsum i.val
      have hj := hsum j.val
      omega
  have : Finite {i // P i} := Finite.of_injective f hf
  apply hasCoproduct_of_finite_nonzero _ P
  intro i hi
  change ¬ (a ≤ i.val.1 ∧ 0 ≤ i.val.2) at hi
  by_cases hp : i.val.1 < a
  · exact hbelow _ _ hp
  · exact hneg _ _ (lt_of_not_ge (fun hn ↦ hi ⟨le_of_not_gt hp, hn⟩))

end HomologicalComplex₂
