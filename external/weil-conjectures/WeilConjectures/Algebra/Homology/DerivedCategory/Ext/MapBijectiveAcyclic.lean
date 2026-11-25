/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.FiveLemma

/-!
# Comparing `Ext` along an exact functor sending injectives to acyclic objects

Let `F : C ⥤ D` be an exact functor between abelian categories, `C` with enough injectives, and
`u : X' ⟶ F X` a morphism in `D`. Consider the maps
`Ext X Y n ⟶ Ext X' (F Y) n`, `e ↦ u ∘ F(e)`. If they are bijective in degree `0` and
`Ext X' (F I) (n + 1) = 0` for every injective `I` of `C`, then they are bijective in every degree
(`CategoryTheory.Functor.bijective_mapExtComp`). This is the usual dimension shifting.

For instance, for the forgetful functor from sheaves of modules over a ring `Λ` to abelian
sheaves and `u : ℤ_X ⟶ Λ_X`, it identifies `Ext^n(Λ_X, M)` (cohomology computed with sheaves of
`Λ`-modules) with `Hⁿ(X, M)` (cohomology of the underlying abelian sheaf).
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {X : C} {X' : D} (u : X' ⟶ F.obj X)

/-- The map `Ext X Y n ⟶ Ext X' (F Y) n`, `e ↦ u ∘ F(e)`. -/
noncomputable def Functor.mapExtComp (Y : C) (n : ℕ) : Ext X Y n →+ Ext X' (F.obj Y) n :=
  AddMonoidHom.mk' (fun e ↦ (Ext.mk₀ u).comp (e.mapExactFunctor F) (zero_add n))
    fun e e' ↦ by rw [Ext.mapExactFunctor_add, Ext.comp_add]

lemma Functor.mapExtComp_apply (Y : C) (n : ℕ) (e : Ext X Y n) :
    F.mapExtComp u Y n e = (Ext.mk₀ u).comp (e.mapExactFunctor F) (zero_add n) :=
  rfl

lemma Functor.mapExtComp_comp_mk₀ {Y Z : C} (g : Y ⟶ Z) {n : ℕ} (e : Ext X Y n) :
    F.mapExtComp u Z n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (F.mapExtComp u Y n e).comp (Ext.mk₀ (F.map g)) (add_zero n) := by
  rw [mapExtComp_apply, mapExtComp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

lemma Functor.mapExtComp_comp_extClass {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (e : Ext X S.X₃ n) :
    F.mapExtComp u S.X₁ (n + 1) (e.comp hS.extClass rfl) =
      (F.mapExtComp u S.X₃ n e).comp (hS.map_of_exact F).extClass rfl := by
  rw [mapExtComp_apply, mapExtComp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Ext.subsingleton_of_injective in
/-- **Dimension shifting.** If `e ↦ u ∘ F(e)` is bijective in degree `0`, and `Ext X' (F I) (n + 1)`
vanishes for every injective `I`, then it is bijective in every degree. -/
theorem Functor.bijective_mapExtComp [EnoughInjectives C]
    (h0 : ∀ Y, Function.Bijective (F.mapExtComp u Y 0))
    (hacyc : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext X' (F.obj I) (n + 1)))
    (Y : C) (n : ℕ) : Function.Bijective (F.mapExtComp u Y n) := by
  induction n generalizing Y with
  | zero => exact h0 Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have : Subsingleton (Ext X' (S.map F).X₂ (n + 1)) := hacyc S.X₂ n
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtComp u S.X₂ n) (F.mapExtComp u S.X₃ n) (F.mapExtComp u S.X₁ (n + 1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X' (hS.map_of_exact F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact F) y₁ (by subsingleton) rfl)
    · exact AddMonoidHom.ext fun e ↦ (F.mapExtComp_comp_mk₀ u S.g e).symm
    · exact AddMonoidHom.ext fun e ↦ (F.mapExtComp_comp_extClass u hS e).symm

end CategoryTheory
