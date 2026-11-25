/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import all Mathlib.Algebra.Homology.Localization

/-! # Tensor normalization of a unit-normalized Roos comparison

Source: Stacks Tag 0941, product-cone comparison and ordinary-limit inclusion.
(blueprint: lem-pur-roos-tensor-normalization).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RoosTensor
universe u d

private theorem factorsh_quotient
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

section SquareHelpers

variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory Ap] [HasDerivedCategory Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (H : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [H.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
  [x.PreservesKInjectiveComplexes]

end SquareHelpers

section Limits

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  (F : A ⥤ B) [F.Additive]

attribute [local implicit_reducible] roosTowerAction HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  NatTrans.mapHomologicalComplex
  HomologicalComplex.coneOfHasLimitEval strictTowerLimitIso

private abbrev complexF := F.mapHomologicalComplex (.up ℤ)
private abbrev limitComparison (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexF F).obj (limit K.asFunctor) ⟶ limit ((roosTowerAction F).obj K).asFunctor :=
  limit.post K.asFunctor (complexF F)

private theorem comparison_inclusion (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexF F).map (roosι K) ≫ roosAdditiveComparison F K =
      limitComparison F K ≫ roosι ((roosTowerAction F).obj K) := by
  have ha (n : ℕ) : limit.π K.asFunctor (op (n + 1)) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = limit.π K.asFunctor (op n) :=
    limit.w K.asFunctor _
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ ((roosTowerAction F).obj K) p).hom).mp
  have h := roosAdditiveComparison_augmentation F K (limit K.asFunctor)
    (fun n ↦ limit.π K.asFunctor (op n)) ha p
  change ((complexF F).map (roosι K) ≫ roosAdditiveComparison F K).f (p + 1) ≫ _ = _
    at h
  rw [h]
  simp only [HomologicalComplex.comp_f, Category.assoc, roosι_χ]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    erw [biprod.lift_fst, comp_zero]
  · simp only [Category.assoc, biprod.lift_snd]
    have hl : limitComparison F K ≫
        Pi.lift (fun n : ℕ ↦ limit.π ((roosTowerAction F).obj K).asFunctor (op n)) =
      Pi.lift (fun n : ℕ ↦ (complexF F).map (limit.π K.asFunctor (op n))) := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc]
      erw [Pi.lift_comp_π, Pi.lift_comp_π]
      exact limit.post_π K.asFunctor (complexF F) (op n)
    exact congrArg (fun z ↦ z.f (p + 1)) hl.symm

variable [PreservesLimitsOfShape ℕᵒᵖ F]

end Limits

section Coordinates

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  (F : A ⥤ B) [F.Additive]

end Coordinates

section Derived

variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape ℕᵒᵖ F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes]

end Derived
end CategoryTheory.RoosTensor
