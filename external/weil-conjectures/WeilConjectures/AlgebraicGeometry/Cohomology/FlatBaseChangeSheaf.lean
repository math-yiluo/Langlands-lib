/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import WeilConjectures.AlgebraicGeometry.Modules.StalkPullback

/-!
# Cohomology and flat base change, for sheaves

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

section FlatPullback

/-- A morphism of `𝒪_X`-modules which is injective on all stalks is a monomorphism. -/
lemma mono_of_injective_stalkLinearMap {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x, Function.Injective (φ.stalkLinearMap x)) : Mono φ := by
  refine ShortComplex.Exact.mono_g (S := ShortComplex.mk (0 : 0 ⟶ M) φ zero_comp) ?_ rfl
  rw [exact_iff_stalkFunctor]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact (h x (ha.trans (map_zero _).symm)).symm

/-- A monomorphism of `𝒪_X`-modules is injective on stalks. -/
lemma injective_stalkLinearMap_of_mono {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (x : X) : Function.Injective (φ.stalkLinearMap x) :=
  (AddCommGrpCat.mono_iff_injective ((stalkFunctor x).map φ)).mp inferInstance

attribute [local instance] stalkAlgebra stalkModule in
/-- **Pullback along a flat morphism preserves monomorphisms**: on stalks it is the base change
`𝒪_{T,t} ⊗_{𝒪_{S,g t}} -` along the flat local ring map `𝒪_{S,g t} ⟶ 𝒪_{T,t}`. -/
theorem mono_pullback_map {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] {M N : S.Modules}
    (φ : M ⟶ N) [Mono φ] : Mono ((pullback g).map φ) := by
  refine mono_of_injective_stalkLinearMap _ fun t ↦ ?_
  have : Module.Flat (S.presheaf.stalk (g t)) (T.presheaf.stalk t) := Flat.stalkMap g t
  have h₁ : Function.Injective (LinearMap.lTensor (T.presheaf.stalk t)
      (φ.stalkLinearMap (g t))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (injective_stalkLinearMap_of_mono φ _)
  intro a b hab
  obtain ⟨a, rfl⟩ := (bijective_pullbackStalkMap g t M).2 a
  obtain ⟨b, rfl⟩ := (bijective_pullbackStalkMap g t M).2 b
  rw [← pullbackStalkMap_naturality, ← pullbackStalkMap_naturality] at hab
  exact congrArg _ (h₁ ((bijective_pullbackStalkMap g t N).1 hab))

instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] : (pullback g).PreservesMonomorphisms :=
  ⟨fun φ _ ↦ mono_pullback_map g φ⟩

instance {S T : Scheme.{u}} (g : T ⟶ S) : PreservesFiniteColimits (pullback g) :=
  have := (pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

/-- Pullback along a flat morphism is exact. -/
instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] : (pullback g).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] : PreservesFiniteLimits (pullback g) :=
  (pullback g).preservesFiniteLimits_of_preservesHomology

/-- The direct image along a flat morphism preserves injective objects, its left adjoint being
exact. -/
instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] (I : T.Modules) [Injective I] :
    Injective ((pushforward g).obj I) :=
  Injective.injective_of_adjoint (pullbackPushforwardAdjunction g) I

end FlatPullback

end AlgebraicGeometry.Scheme.Modules
