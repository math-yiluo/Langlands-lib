/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Full faithfulness of base change along a universal homeomorphism, for rings

Let `B` be an `A`-algebra which is a universal homeomorphism (i.e. `Spec B ⟶ Spec A` is one).
Then for an étale `A`-algebra `E₁` and any `A`-algebra `E₂`, every `B`-algebra map
`B ⊗[A] E₁ →ₐ[B] B ⊗[A] E₂` is the base change of a unique `A`-algebra map `E₁ →ₐ[A] E₂`.
This is the ring-theoretic form of
`AlgebraicGeometry.Scheme.Hom.existsUnique_of_isPullback`, obtained by applying `Spec`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.IsUniversalHomeomorphism

open AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.IsUniversalHomeomorphism A B]
  {E₁ E₂ : Type u} [CommRing E₁] [CommRing E₂] [Algebra A E₁] [Algebra A E₂]
  [Algebra.Etale A E₁]

/-- **Full faithfulness of base change along a universal homeomorphism** for rings: if `E₁` is
étale over `A`, every `B`-algebra map `B ⊗[A] E₁ →ₐ[B] B ⊗[A] E₂` is the base change of a unique
`A`-algebra map `E₁ →ₐ[A] E₂`. -/
theorem existsUnique_algHom (ψ : B ⊗[A] E₁ →ₐ[B] B ⊗[A] E₂) :
    ∃! φ : E₁ →ₐ[A] E₂, Algebra.TensorProduct.map (AlgHom.id B B) φ = ψ := by
  -- The universal homeomorphism `f: Spec B ⟶ Spec A` and the étale `v₁: Spec E₁ ⟶ Spec A`.
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let v₁ : Spec (.of E₁) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A E₁))
  let v₂ : Spec (.of E₂) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A E₂))
  have hv₁ : AlgebraicGeometry.Etale v₁ :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  -- The pullback squares `Spec (B ⊗[A] Eᵢ) = Spec Eᵢ ×_{Spec A} Spec B`.
  let p₁ : Spec (.of (B ⊗[A] E₁)) ⟶ Spec (.of E₁) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  let q₁ : Spec (.of (B ⊗[A] E₁)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let p₂ : Spec (.of (B ⊗[A] E₂)) ⟶ Spec (.of E₂) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  let q₂ : Spec (.of (B ⊗[A] E₂)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  have h₁ : IsPullback p₁ q₁ v₁ f :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E₁)).flip
  have h₂ : IsPullback p₂ q₂ v₂ f :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E₂)).flip
  -- The `X`-morphism `Spec ψ`.
  let a : Spec (.of (B ⊗[A] E₂)) ⟶ Spec (.of (B ⊗[A] E₁)) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have ha : a ≫ q₁ = q₂ := by
    simp only [a, q₁, q₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext b
    simpa using ψ.commutes b
  -- Translate between `A`-algebra maps `E₁ → E₂` and `Y`-morphisms `Spec E₂ ⟶ Spec E₁`.
  have key : ∀ φ : E₁ →ₐ[A] E₂, Algebra.TensorProduct.map (AlgHom.id B B) φ = ψ ↔
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ v₁ = v₂ ∧
        p₂ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) = a ≫ p₁) := by
    intro φ
    have hφv : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ v₁ = v₂ := by
      simp only [v₁, v₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      simp
    simp only [hφv, true_and, p₁, p₂, a, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
    constructor
    · rintro rfl
      ext x
      simp
    · intro h
      have h' : ∀ x, ψ (1 ⊗ₜ x) = 1 ⊗ₜ φ x := fun x ↦ (congr($(h).hom x)).symm
      refine Algebra.TensorProduct.ext' fun b x ↦ ?_
      rw [show b ⊗ₜ[A] x = b • (1 ⊗ₜ[A] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, h']
      simp [TensorProduct.smul_tmul']
  obtain ⟨g, ⟨hg, hga⟩, huniq⟩ := Scheme.Hom.existsUnique_of_isPullback f v₂ v₁ h₂ h₁ a ha
  obtain ⟨φ₀, rfl⟩ := Spec.map_surjective g
  have hφ₀ : (CommRingCat.ofHom (algebraMap A E₁) ≫ φ₀) = CommRingCat.ofHom (algebraMap A E₂) := by
    rw [← Spec.map_inj, Spec.map_comp]
    exact hg
  let φ : E₁ →ₐ[A] E₂ :=
    { φ₀.hom with
      commutes' := fun x ↦ by
        have := congr($hφ₀ x)
        simpa using this }
  have hφ : CommRingCat.ofHom φ.toRingHom = φ₀ := rfl
  refine ⟨φ, (key φ).mpr ⟨by rw [hφ]; exact hg, by rw [hφ]; exact hga⟩, fun φ' hφ' ↦ ?_⟩
  obtain ⟨h1, h2⟩ := (key φ').mp hφ'
  have := Spec.map_inj.mp (huniq _ ⟨h1, h2⟩)
  ext x
  exact congr($(this).hom x)

end Algebra.IsUniversalHomeomorphism
