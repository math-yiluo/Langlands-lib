/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Faithfulness on completed coefficient sheaves in degree zero
Source: Stacks 06XS(2), and diagonal trace proof paragraph (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem single_map_injective
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {M N : A}
    (f g : (DerivedCategory.singleFunctor A 0).obj M ⟶
      (DerivedCategory.singleFunctor A 0).obj N)
    (h : F.mapDerivedCategory.map f = F.mapDerivedCategory.map g) : f = g := by
  obtain ⟨f, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective f
  obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective g
  congr 1
  apply F.map_injective
  apply (DerivedCategory.singleFunctor B 0).map_injective
  apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).hom.app M)).1
  have hf := (F.mapDerivedCategorySingleFunctor 0).hom.naturality f
  have hg := (F.mapDerivedCategorySingleFunctor 0).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← hf, ← hg, h]

/-- Restriction to discrete scalars detects equality on maps between completed
coefficient sheaves in degree zero.
Source: Stacks 06XS(2); diagonal trace proof paragraph (2)
(blueprint: lem-sfb-diagonal-trace-single-faithful).
Proof: ordinary scalar restriction retains every underlying section map, so is faithful.
Fullness of the degree-zero derived embedding writes the two arrows as sheaf maps.
Naturality of its exact-functor comparison and faithfulness of the degree-zero embedding
reduce their equality to ordinary scalar restriction. -/
theorem diagonalTrace_single_map_injective (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] {M N : DiagonalCompleted l X}
    (f g : (DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).obj M ⟶
      (DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).obj N)
    (h : (diagonalCompletedUnderlying l X).map f =
      (diagonalCompletedUnderlying l X).map g) : f = g := by
  let F := diagonalCompletedRestriction l X
  have : F.Faithful := ⟨fun {M N} f g h ↦ by
    ext U x
    have hu := congrArg (fun k ↦ (k.hom.app U).hom x) h
    exact hu⟩
  exact single_map_injective F f g h

end AlgebraicGeometry.ProEtale.DiagonalTrace
