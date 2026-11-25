/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Finiteness of `Ext`-groups and of morphisms along exact sequences

In an exact sequence `A ⟶ B ⟶ C` of additive groups, `B` is finite if `A` and `C` are
(`AddMonoidHom.finite_of_exact`). We apply this to the long exact sequences of `Ext`-groups
attached to a short exact sequence (`CategoryTheory.Abelian.Ext.finite_of_shortExact`) and to
the exact sequences of morphisms attached to a distinguished triangle
(`CategoryTheory.Pretriangulated.Triangle.finite_hom_obj₂_of_coyoneda`,
`CategoryTheory.Pretriangulated.Triangle.finite_hom_obj₂_of_yoneda`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

/-- In an exact sequence `A ⟶ B ⟶ C` of additive groups, `B` is finite if `A` and `C` are. -/
lemma AddMonoidHom.finite_of_exact {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (g : A →+ B) (f : B →+ C) (hfg : ∀ b, f b = 0 → ∃ a, g a = b) [Finite A] [Finite C] :
    Finite B := by
  have hs : ∀ c : Set.range f, ∃ b, f b = c := fun c ↦ c.2
  choose s hs using hs
  refine Finite.of_surjective (fun x : A × Set.range f ↦ g x.1 + s x.2) fun b ↦ ?_
  obtain ⟨a, ha⟩ := hfg (b - s ⟨f b, b, rfl⟩) (by simp [hs])
  exact ⟨(a, ⟨f b, b, rfl⟩), by simp [ha]⟩

namespace CategoryTheory

namespace Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the group `Extⁿ⁺¹(X₃, Y)` is finite if
`Extⁿ(X₁, Y)` and `Extⁿ⁺¹(X₂, Y)` are. -/
lemma finite_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n : ℕ)
    [Finite (Ext S.X₁ Y n)] [Finite (Ext S.X₂ Y (n + 1))] : Finite (Ext S.X₃ Y (n + 1)) :=
  AddMonoidHom.finite_of_exact (hS.extClass.precomp Y (add_comm 1 n))
    ((mk₀ S.g).precomp Y (zero_add (n + 1)))
    fun x hx ↦ contravariant_sequence_exact₃ hS Y x hx (add_comm 1 n)

/-- `Extⁿ(⨁ Xⱼ, Y)` is finite if every `Extⁿ(Xⱼ, Y)` is, for a finite biproduct. -/
lemma finite_of_isBilimit {J : Type*} [Finite J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) [∀ j, Finite (Ext (X j) Y n)] :
    Finite (Ext c.pt Y n) :=
  have := Fintype.ofFinite J
  Finite.of_equiv _ (biproductAddEquiv hc Y n).toEquiv.symm

end Abelian.Ext

section Triangle

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

open Pretriangulated

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and an object `A`, the set of morphisms
`A ⟶ X₂` is finite if the sets of morphisms `A ⟶ X₁` and `A ⟶ X₃` are. -/
lemma Pretriangulated.Triangle.finite_hom_obj₂_of_coyoneda (T : Triangle D)
    (hT : T ∈ distTriang D) (A : D) [Finite (A ⟶ T.obj₁)] [Finite (A ⟶ T.obj₃)] :
    Finite (A ⟶ T.obj₂) :=
  AddMonoidHom.finite_of_exact (CategoryTheory.Preadditive.rightComp A T.mor₁)
    (CategoryTheory.Preadditive.rightComp A T.mor₂)
    fun f hf ↦ (Triangle.coyoneda_exact₂ T hT f hf).imp fun _ h ↦ h.symm

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and an object `B`, the set of morphisms
`X₂ ⟶ B` is finite if the sets of morphisms `X₁ ⟶ B` and `X₃ ⟶ B` are. -/
lemma Pretriangulated.Triangle.finite_hom_obj₂_of_yoneda (T : Triangle D)
    (hT : T ∈ distTriang D) (B : D) [Finite (T.obj₁ ⟶ B)] [Finite (T.obj₃ ⟶ B)] :
    Finite (T.obj₂ ⟶ B) :=
  AddMonoidHom.finite_of_exact (CategoryTheory.Preadditive.leftComp B T.mor₂)
    (CategoryTheory.Preadditive.leftComp B T.mor₁)
    fun f hf ↦ (Triangle.yoneda_exact₂ T hT f hf).imp fun _ h ↦ h.symm

end Triangle

end CategoryTheory
