/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact functors on `Ext`-groups, by dimension shifting

In an abelian category `C` with enough injectives every `Ext`-class of positive degree is the
image of a class of lower degree under the connecting map of an injective presentation. This
reduces statements about the maps `Ext^n(X, Y) ⟶ Ext^n(E X, E Y)` induced by exact functors
`E` to degree `0`.

## Main statements

- `CategoryTheory.Abelian.Ext.mk₀_comp_mapExactFunctor_of_iso`: isomorphic exact functors
  induce the same maps on `Ext`-groups, up to the isomorphism.
- `CategoryTheory.Abelian.Ext.bijective_mk₀_comp_mapExactFunctor`: if `e : S ⟶ E A`
  induces a bijection `(A ⟶ N) ≃ (S ⟶ E N)` for all `N`, and `Ext^{n + 1}(S, E I) = 0` for
  injective `I`, then `x ↦ e ∘ E x` is a bijection `Ext^n(A, N) ≃ Ext^n(S, E N)`.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

attribute [local instance] Ext.subsingleton_of_injective

/-- Every class of positive degree is the image of a connecting map out of an injective
presentation. -/
lemma exists_comp_extClass_of_injective [EnoughInjectives C] {X Y : C} {n : ℕ}
    (x : Ext X Y (n + 1)) :
    ∃ (I : InjectivePresentation Y) (y : Ext X (cokernel I.f) n),
      y.comp (ShortComplex.ShortExact.extClass (S := ShortComplex.mk _ _ (cokernel.condition I.f))
        { exact := ShortComplex.exact_cokernel I.f }) rfl = x := by
  let I : InjectivePresentation Y := Classical.arbitrary _
  have := I.injective
  obtain ⟨y, hy⟩ := covariant_sequence_exact₁ X
    (S := ShortComplex.mk _ _ (cokernel.condition I.f)) { exact := ShortComplex.exact_cokernel I.f }
    x (Subsingleton.elim _ _) rfl
  exact ⟨I, y, hy⟩

/-- Pushing `Ext`-classes forward along isomorphic exact functors gives the same class up to the
isomorphism. -/
lemma mk₀_comp_mapExactFunctor_of_iso [EnoughInjectives C] {F G : C ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ≅ G) {X Y : C} {n : ℕ}
    (x : Ext X Y n) :
    (mk₀ (τ.hom.app X)).comp (x.mapExactFunctor G) (zero_add n) =
      (x.mapExactFunctor F).comp (mk₀ (τ.hom.app Y)) (add_zero n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective X Y).2 x
    rw [mapExactFunctor_mk₀, mapExactFunctor_mk₀, mk₀_comp_mk₀, mk₀_comp_mk₀,
      τ.hom.naturality]
  | succ n ih =>
    obtain ⟨I, y, rfl⟩ := exists_comp_extClass_of_injective x
    set S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_extClass,
      mapExactFunctor_extClass,
      ← comp_assoc (mk₀ (τ.hom.app X)) _ _ (zero_add n) rfl (by omega), ih,
      comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega),
      comp_assoc _ _ _ rfl (add_zero 1) (by omega)]
    congr 1
    exact (ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact F) (hS.map_of_exact G)
      (S.mapNatTrans τ.hom)).symm

/-- Let `E : C ⥤ D` be an exact functor, `A : C` and `e : S ⟶ E A` such that `f ↦ e ≫ E f` is a
bijection `(A ⟶ N) ≃ (S ⟶ E N)` for all `N`, and such that `Ext^{n + 1}(S, E I) = 0` for every
injective `I`. Then `x ↦ e ∘ E x` is a bijection `Ext^n(A, N) ≃ Ext^n(S, E N)` in every degree:
both sides are effaceable δ-functors in `N` which agree in degree `0`. -/
theorem bijective_mk₀_comp_mapExactFunctor [EnoughInjectives C] (E : C ⥤ D) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] {A : C} {S : D} (e : S ⟶ E.obj A)
    (h₀ : ∀ N : C, Function.Bijective (fun f : A ⟶ N ↦ e ≫ E.map f))
    (h₁ : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext S (E.obj I) (n + 1)))
    (N : C) (n : ℕ) :
    Function.Bijective (fun x : Ext A N n ↦ (mk₀ e).comp (x.mapExactFunctor E) (zero_add n)) := by
  induction n generalizing N with
  | zero =>
    have : (fun x : Ext A N 0 ↦ (mk₀ e).comp (x.mapExactFunctor E) (zero_add 0)) =
        (fun f ↦ mk₀ f) ∘ (fun f : A ⟶ N ↦ e ≫ E.map f) ∘ homEquiv₀ := by
      ext x
      obtain ⟨f, rfl⟩ := (mk₀_bijective A N).2 x
      simp [mapExactFunctor_mk₀, mk₀_comp_mk₀, homEquiv₀]
    rw [this]
    exact (mk₀_bijective _ _).comp ((h₀ N).comp homEquiv₀.bijective)
  | succ n ih =>
    let I : InjectivePresentation N := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let c (M : C) (m : ℕ) : Ext A M m →+ Ext S (E.obj M) m :=
      ((mk₀ e).precomp (E.obj M) (zero_add m)).comp (E.mapExtAddHom A M m)
    have hc (M : C) (m : ℕ) (x : Ext A M m) :
        c M m x = (mk₀ e).comp (x.mapExactFunctor E) (zero_add m) := rfl
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
        ((mk₀ T.g).postcomp A (add_zero n)) (hT.extClass.postcomp A rfl)
        ((mk₀ (E.map T.g)).postcomp S (add_zero n))
        ((hT.map_of_exact E).extClass.postcomp S rfl)
        (c T.X₂ n) (c T.X₃ n) (c T.X₁ (n + 1))
        (by
          ext x
          simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.flip_apply,
            bilinearComp_apply_apply, hc]
          rw [mapExactFunctor_comp, mapExactFunctor_mk₀, comp_assoc_of_third_deg_zero])
        (by
          ext x
          change ((mk₀ e).comp (x.mapExactFunctor E) (zero_add n)).comp
              (hT.map_of_exact E).extClass rfl =
            (mk₀ e).comp ((x.comp hT.extClass rfl).mapExactFunctor E) (zero_add (n + 1))
          rw [mapExactFunctor_comp, mapExactFunctor_extClass,
            comp_assoc _ _ _ (zero_add n) rfl (by omega)])
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (covariant_sequence_exact₃' A hT n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (covariant_sequence_exact₃' S (hT.map_of_exact E) n (n + 1) rfl))
        (ih _).surjective (ih _)
        (fun x₁ ↦ covariant_sequence_exact₁ _ hT x₁ (Subsingleton.elim _ _) rfl)
        (fun y₁ ↦ covariant_sequence_exact₁ _ (hT.map_of_exact E) y₁
          (@Subsingleton.elim (Ext S (E.obj T.X₂) (n + 1)) (h₁ T.X₂ n) _ _) rfl)

end CategoryTheory.Abelian.Ext
