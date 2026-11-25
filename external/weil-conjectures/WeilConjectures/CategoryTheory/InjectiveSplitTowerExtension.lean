/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

@[expose] public section
universe u
open CategoryTheory
namespace CategoryTheory

/-- Compatible lifting for a split injective tower along one monomorphism.
At level zero use injectivity. At a successor level, extend the given component arbitrarily
using injectivity, then correct its transition error using a section of the split transition.
The correction vanishes on the original tower. Recursion gives adjacent compatibility,
and `NatTrans.ofOpSequence` gives compatibility with every tower map.
Related inverse-system construction: Stacks Project Tag 07KW.
(blueprint: lem-pc-injective-split-tower-extension) -/
theorem injective_split_tower_extension (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hI : ∀ n : ℕ, Injective (I.obj (Opposite.op n)))
    (hp : ∀ n : ℕ, IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op))
    {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) [Mono f] (g : A ⟶ I) :
    ∃ h : B ⟶ I, f ≫ h = g := by
  classical
  have : ∀ n : ℕ, Injective (I.obj (Opposite.op n)) := hI
  have : ∀ n : ℕ, IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op) := hp
  let L (n : ℕ) := {h : B.obj (Opposite.op n) ⟶ I.obj (Opposite.op n) //
    f.app (Opposite.op n) ≫ h = g.app (Opposite.op n)}
  let start : L 0 := ⟨Injective.factorThru (g.app _) (f.app _),
    Injective.comp_factorThru _ _⟩
  let next (n : ℕ) (h : L n) : L (n + 1) := by
    let k := (homOfLE (Nat.le_add_right n 1)).op
    let p := I.map k
    let s := section_ p
    let t := Injective.factorThru (g.app (Opposite.op (n + 1)))
      (f.app (Opposite.op (n + 1)))
    let b := B.map k ≫ h.val
    refine ⟨t + (b - t ≫ p) ≫ s, ?_⟩
    have hb : f.app (Opposite.op (n + 1)) ≫ b =
        g.app (Opposite.op (n + 1)) ≫ p := by
      dsimp [b, p]
      rw [← Category.assoc, ← f.naturality, Category.assoc, h.property, g.naturality]
    simp only [t, Preadditive.comp_add, Preadditive.comp_sub, ← Category.assoc,
      Injective.comp_factorThru, hb, sub_self, Limits.zero_comp, add_zero]
  let lifts : ∀ n, L n := fun n ↦ Nat.rec start next n
  have compatible (n : ℕ) :
      B.map (homOfLE (Nat.le_add_right n 1)).op ≫ (lifts n).val =
        (lifts (n + 1)).val ≫ I.map (homOfLE (Nat.le_add_right n 1)).op := by
    change _ = (next n (lifts n)).val ≫ _
    dsimp [next]
    simp only [Preadditive.add_comp, Category.assoc, IsSplitEpi.id,
      Category.comp_id]
    abel
  refine ⟨NatTrans.ofOpSequence (fun n ↦ (lifts n).val) compatible, ?_⟩
  apply NatTrans.ext
  funext X
  exact (lifts X.unop).property

end CategoryTheory
