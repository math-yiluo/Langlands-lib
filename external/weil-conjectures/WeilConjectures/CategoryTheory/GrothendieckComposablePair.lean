/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-!
# Composable pairs and acyclicity

Source: blueprint, node def-sp-composite-acyclicity; Stacks Project, Derived Categories,
Section 13.22, Lemma 13.22.1 (Tag 015M) (blueprint: def-sp-composite-acyclicity).

## Main definitions

- `CategoryTheory.GrothendieckComposablePair`: a pair of left exact additive functors.
- `CategoryTheory.GrothendieckComposablePair.SendsInjectivesToAcyclics`: its acyclicity
  condition.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

/-- A composable pair of left exact additive functors between Grothendieck abelian
categories (Stacks Project, Tag 015M). (blueprint: def-sp-composite-acyclicity) -/
structure GrothendieckComposablePair
    (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [Category.{v₃} C] [Abelian C] [IsGrothendieckAbelian.{v₃} C] where
  F : A ⥤ B
  G : B ⥤ C
  [additiveF : F.Additive]
  [additiveG : G.Additive]
  [leftExactF : PreservesFiniteLimits F]
  [leftExactG : PreservesFiniteLimits G]

/-- The first functor of a composable pair sends injectives to objects acyclic for the
second precisely when all positive right derived functors of the second vanish on their
images (Stacks Project, Tag 015M). (blueprint: def-sp-composite-acyclicity) -/
def GrothendieckComposablePair.SendsInjectivesToAcyclics
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [Category.{v₃} C] [Abelian C] [IsGrothendieckAbelian.{v₃} C]
    (P : GrothendieckComposablePair A B C) : Prop := by
  letI := P.additiveF
  letI := P.additiveG
  exact P.F.IsAcyclicComposablePair P.G

end CategoryTheory
