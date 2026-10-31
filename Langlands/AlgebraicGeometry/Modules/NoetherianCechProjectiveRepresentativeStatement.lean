/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Adapted by Worker 137: Prop-valued interface strengthened to retain the
original-base cycle tests from the source construction; definition imports
and unused proof binders adjusted.
Source: Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

def NoetherianCechProjectiveRepresentativeStatement : Prop :=
  ∀    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [IsProper π] [Flat π] (M : X.Modules)
    (_htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (n : ℕ) (_hn : Fintype.card 𝒰.ι ≤ n + 1),
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (_ : ∀ i, (OModulePresheaf.ofModules π M).d 𝒰 i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
      (Θ : ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ), A ⊗[R] K i →ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i),
      (∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0) ∧
      (∀ y : (OModulePresheaf.ofModules π M).cochain 𝒰 0,
        (OModulePresheaf.ofModules π M).d 𝒰 0 y = 0 →
        ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y) ∧
      (∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 →
        φ (i + 1) x ∈ LinearMap.range ((OModulePresheaf.ofModules π M).d 𝒰 i) →
        x ∈ LinearMap.range (δ i)) ∧
      (∀ (i : ℕ) (y : (OModulePresheaf.ofModules π M).cochain 𝒰 (i + 1)),
        (OModulePresheaf.ofModules π M).d 𝒰 (i + 1) y = 0 →
        ∃ x : K (i + 1), δ (i + 1) x = 0 ∧
          φ (i + 1) x - y ∈ LinearMap.range ((OModulePresheaf.ofModules π M).d 𝒰 i)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (∀ i : ℕ, Θ A (i + 1) ∘ₗ (δ i).baseChange A
          = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
            ∘ₗ Θ A i) ∧
        (∀ (i : ℕ) (a : A) (k : K i) (s : 𝒰.Idx i),
          Θ A i (a ⊗ₜ[R] k) s
            = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
                (𝒰.baseChange_inter_le π A s)
                ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                  (𝒰.inter s)).hom (φ i k s))) ∧
        (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → Θ A 0 x = 0 → x = 0) ∧
        (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) 0,
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) 0 y = 0 →
          ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ Θ A 0 x = y) ∧
        (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
          Θ A (i + 1) x ∈ LinearMap.range
            ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i) →
          x ∈ LinearMap.range ((δ i).baseChange A)) ∧
        (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) (i + 1)),
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) (i + 1) y = 0 →
          ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
            Θ A (i + 1) x - y ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i))

end Langlands.AlgebraicGeometry.Modules
