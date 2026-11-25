/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-! Exact-functor Ext comparison by a degree-zero generator and acyclic injectives.
(blueprint: lem-sfb-finite-derived-restriction-bijective). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

section AbstractComparison
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
  (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  {F : B} {P : A} (η : F ⟶ U.obj P)

def restrictionClass (M : A) (n : ℕ) : Ext.{wA} P M n →+ Ext.{wB} F (U.obj M) n :=
  ((Ext.mk₀ η).precomp (U.obj M) (zero_add n)).comp (U.mapExtAddHom P M n)

theorem restrictionClass_comp {M N : A} {a b c : ℕ}
    (x : Ext.{wA} P M a) (y : Ext.{wA} M N b) (h : a + b = c) :
    restrictionClass U η N c (x.comp y h) =
      (restrictionClass U η M a x).comp (y.mapExactFunctor U) h := by
  change (Ext.mk₀ η).comp ((x.comp y h).mapExactFunctor U) (zero_add c) =
    ((Ext.mk₀ η).comp (x.mapExactFunctor U) (zero_add a)).comp
      (y.mapExactFunctor U) h
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by omega)).symm

attribute [local instance] Ext.subsingleton_of_injective in
theorem restrictionClass_bijective [EnoughInjectives A]
    (hzero : ∀ M : A, Function.Bijective (fun f : P ⟶ M ↦ η ≫ U.map f))
    (hacyc : ∀ (I : A) [Injective I] (n : ℕ),
      Subsingleton (Ext.{wB} F (U.obj I) (n + 1)))
    (n : ℕ) (M : A) : Function.Bijective (restrictionClass U η M n) := by
  induction n generalizing M with
  | zero =>
    have hc : (restrictionClass U η M 0) ∘ Ext.mk₀ =
        Ext.mk₀ ∘ (fun f : P ⟶ M ↦ η ≫ U.map f) := by
      funext f
      change (Ext.mk₀ η).comp ((Ext.mk₀ f).mapExactFunctor U) (zero_add 0) = _
      rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
      rfl
    refine (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).1 ?_
    rw [hc]
    exact (Ext.mk₀_bijective _ _).comp (hzero M)
  | succ n ih =>
    let I : InjectivePresentation M := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map U).ShortExact := hT.map_of_exact U
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ T.g).postcomp _ (add_zero n)) (hT.extClass.postcomp _ rfl)
      ((Ext.mk₀ (U.map T.g)).postcomp _ (add_zero n)) (hS.extClass.postcomp _ rfl)
      (restrictionClass U η I.J n) (restrictionClass U η T.X₃ n)
      (restrictionClass U η M (n + 1))
      (AddMonoidHom.ext fun x ↦ by
        change (restrictionClass U η T.X₂ n x).comp (Ext.mk₀ (U.map T.g))
          (add_zero n) = restrictionClass U η T.X₃ n (x.comp (Ext.mk₀ T.g) (add_zero n))
        simpa only [Ext.mapExactFunctor_mk₀] using
          (restrictionClass_comp U η x (Ext.mk₀ T.g) (add_zero n)).symm)
      (AddMonoidHom.ext fun x ↦ by
        change (restrictionClass U η T.X₃ n x).comp hS.extClass rfl =
          restrictionClass U η T.X₁ (n + 1) (x.comp hT.extClass rfl)
        simpa only [Ext.mapExactFunctor_extClass] using
          (restrictionClass_comp U η x hT.extClass rfl).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hT n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      (ih I.J).2 (ih T.X₃)
      (fun x ↦ Ext.covariant_sequence_exact₁ _ hT x (Ext.eq_zero_of_injective _) rfl)
      (fun y ↦ Ext.covariant_sequence_exact₁ _ hS y
        (@Subsingleton.elim _ (hacyc I.J n) _ _) rfl)
end AbstractComparison
end AlgebraicGeometry.ProEtale.DiagonalTrace
