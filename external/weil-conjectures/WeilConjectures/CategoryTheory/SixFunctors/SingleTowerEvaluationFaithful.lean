/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Evaluation detects equality between single towers

Source: Stacks Project, Tag 06XS(2), and the diagonal trace proof, paragraph (2).
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory

/-- Evaluation detects equality between morphisms of towers placed in degree zero.
Source: Stacks 06XS(2); diagonal trace proof paragraph (2)
(blueprint: lem-sfb-single-tower-evaluation-faithful).
Proof: fullness writes both derived arrows as single images of actual tower maps.
Naturality of the single/evaluation comparison and faithfulness of the single functor
show that each component agrees. Extensionality of natural transformations gives
equality of tower maps, and applying the single functor gives the result. -/
theorem singleTowerEvaluationFaithful
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {M N : ℕᵒᵖ ⥤ A}
    (f g : (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj M ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj N)
    (h : ∀ n : ℕ,
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map f =
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map g) : f = g := by
  obtain ⟨f, rfl⟩ := (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map_surjective f
  obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map_surjective g
  congr 1
  ext n
  apply (DerivedCategory.singleFunctor A 0).map_injective
  have hn := h n.unop
  have hf := (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategorySingleFunctor 0).hom.naturality f
  have hg := (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategorySingleFunctor 0).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  change _ ≫ _ = _ ≫ (DerivedCategory.singleFunctor A 0).map (f.app n) at hf
  change _ ≫ _ = _ ≫ (DerivedCategory.singleFunctor A 0).map (g.app n) at hg
  apply (cancel_epi
    ((((evaluation ℕᵒᵖ A).obj n).mapDerivedCategorySingleFunctor 0).hom.app M)).1
  rw [← hf, ← hg]
  exact congrArg (fun k ↦ k ≫
    ((((evaluation ℕᵒᵖ A).obj n).mapDerivedCategorySingleFunctor 0).hom.app N)) hn

/-- Transport a degree-zero tower identity through any specified limit square.
Source: diagonal trace proof paragraph (2), final passage to inverse limit
(blueprint: lem-sfb-single-tower-limit-identity).
Proof: evaluation detects equality with the identity by the preceding theorem.
Functoriality sends that identity to the identity. Cancel the invertible comparison
in the given square to conclude. -/
theorem singleTowerLimitIdentity
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {M : ℕᵒᵖ ⥤ A}
    (e : (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj M ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj M)
    (h : ∀ n : ℕ,
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map e = 𝟙 _)
    {D : Type*} [Category D]
    (L : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ D) {K : D}
    (j : K ≅ L.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj M))
    (f : K ⟶ K) (hf : f ≫ j.hom = j.hom ≫ L.map e) : f = 𝟙 K := by
  have he : e = 𝟙 _ := singleTowerEvaluationFaithful A e (𝟙 _)
    (fun n ↦ by rw [Functor.map_id]; exact h n)
  apply (cancel_mono j.hom).1
  simpa only [he, Functor.map_id, Category.comp_id, Category.id_comp] using hf

/-- A specified limit square for a degree-zero tower endomorphism with identity levels.
Source: diagonal trace proof paragraph (2)
(blueprint: lem-sfb-single-tower-limit-identity). -/
structure SingleTowerLimitWitness
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {D : Type*} [Category D] {K : D} (f : K ⟶ K) where
  tower : ℕᵒᵖ ⥤ A
  limitFunctor : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ D
  endomorphism : (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj tower ⟶
    (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj tower
  comparison : K ≅ limitFunctor.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj tower)
  evaluations : ∀ n : ℕ,
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map endomorphism = 𝟙 _
  square : f ≫ comparison.hom = comparison.hom ≫ limitFunctor.map endomorphism

/-- The specified limit square transports the identity to its lower endomorphism.
Source: diagonal trace proof paragraph (2)
(blueprint: lem-sfb-single-tower-limit-identity).
Proof: apply the preceding degree-zero limit identity to the recorded tower and square. -/
theorem SingleTowerLimitWitness.eq_id
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {D : Type*} [Category D] {K : D} {f : K ⟶ K}
    (s : SingleTowerLimitWitness A f) : f = 𝟙 K :=
  singleTowerLimitIdentity A s.endomorphism s.evaluations
    s.limitFunctor s.comparison f s.square

end CategoryTheory
