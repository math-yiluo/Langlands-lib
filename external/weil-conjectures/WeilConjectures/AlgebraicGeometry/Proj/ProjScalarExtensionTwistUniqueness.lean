/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData

/-! Uniqueness part of the normalized scalar-extension twist laws. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem comparison_homEquiv_app
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U)) :
    ((tensorPullbackSectionAdjunction r).homEquiv _ _ (θ j).hom).app U s =
      scalarExtensionTwistSection r θ j U s := by
  rw [Adjunction.homEquiv_apply, Hom.comp_app]
  change (θ j).hom.app (r ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction r).unit.app (twist 𝒜 j)).app U s) = _
  exact congrArg ((θ j).hom.app (r ⁻¹ᵁ U))
    ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction r)).1
      (twist 𝒜 j) U s)

private theorem comparison_denominator_unit
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ)
    (k : ℕ) (b : A) (hb : b ∈ 𝒜 k)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b) (x : r ⁻¹ᵁ U) :
    IsUnit (Localization.mk (ψ b) 1 :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
  -- The normalized image of 1/b is an inverse of the image of b.
  let t : Γ(twist 𝒜 (-(k : ℤ)), U) :=
    ⟨fun y ↦ HomogeneousLocalization.degreePart.mk
        (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨b, hb⟩ (hU y.2) (by omega),
      ProjectiveSpectrum.Twist.isLocallyFraction_mk (by omega)
        (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨b, hb⟩ (fun y ↦ hU y.2)⟩
  have ht (y : U) :
      (t.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk b 1 = Localization.mk 1 1 := by
    change Localization.mk 1 ⟨b, hU y.2⟩ * Localization.mk b 1 = _
    simp only [Localization.mk_mul, one_mul, mul_one, Localization.mk_one]
    exact Localization.mk_self ⟨b, hU y.2⟩
  have H := hθ (-(k : ℤ)) 0 k 1 b (SetLike.one_mem_graded 𝒜) hb (by omega)
    U hU t ht 1 x
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨(scalarExtensionTwistSection r θ (-(k : ℤ)) U t).1 x, ?_⟩
  have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ U)).1 x).val = 1 :=
    HomogeneousLocalization.val_one
  simpa only [one_smul, hOne, map_one, Localization.mk_one, mul_one] using H

/- Local homogeneous fractions and the section-normalized pullback adjunction give uniqueness. -/
theorem scalarExtension_twist_uniqueness
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ θ' : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
      IsScalarExtensionTwistComparison ψ r θ' → θ' = θ := by
  intro θ' hθ'
  funext j
  apply Iso.ext
  apply ((tensorPullbackSectionAdjunction r).homEquiv _ _).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [comparison_homEquiv_app, comparison_homEquiv_app]
  apply Subtype.ext
  funext x
  apply Subtype.ext
  -- A twist section is locally a single homogeneous fraction.
  obtain ⟨V, hxV, e, i, k, hik, a, b, hb, hs⟩ := s.2 ⟨r.base x.1, x.2⟩
  let t : Γ(twist 𝒜 j, V) := (twist 𝒜 j).presheaf.map e.op s
  have hV : V ≤ basicOpen 𝒜 (b : A) := fun y hy ↦ hb ⟨y, hy⟩
  have ht (y : V) :
      (t.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk (b : A) 1 = Localization.mk (a : A) 1 := by
    have hy : (t.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) =
        Localization.mk (a : A) ⟨(b : A), hb y⟩ := congrArg Subtype.val (hs y)
    calc
      _ = Localization.mk (a : A) ⟨(b : A), hb y⟩ *
          Localization.mk (b : A) 1 := congrArg (fun z ↦ z * Localization.mk (b : A) 1) hy
      _ = Localization.mk (b : A) ⟨(b : A), hb y⟩ *
          Localization.mk (a : A) 1 := by simp only [Localization.mk_mul, mul_comm]
      _ = _ := by rw [Localization.mk_self ⟨(b : A), hb y⟩, one_mul]
  let y : r ⁻¹ᵁ V := ⟨x.1, hxV⟩
  have H := hθ j i k a b a.2 b.2 hik V hV t ht 1 y
  have H' := hθ' j i k a b a.2 b.2 hik V hV t ht 1 y
  simp only [one_smul] at H H'
  have hu := comparison_denominator_unit ψ r θ hθ k b b.2 V hV y
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hlocal : (scalarExtensionTwistSection r θ' j V t).1 y =
      (scalarExtensionTwistSection r θ j V t).1 y := by
    apply Subtype.ext
    calc
      _ = ((scalarExtensionTwistSection r θ' j V t).1 y :
          Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          (Localization.mk (ψ b) 1 * v) := by rw [hv, mul_one]
      _ = ((scalarExtensionTwistSection r θ' j V t).1 y :
          Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (ψ b) 1 * v := (mul_assoc _ _ _).symm
      _ = ((scalarExtensionTwistSection r θ j V t).1 y :
          Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (ψ b) 1 * v := by rw [H', H]
      _ = _ := by rw [mul_assoc, hv, mul_one]
  -- Naturality brings the equality on V back to the original point of U.
  have nat (η : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j) :
      (twist ℬ j).presheaf.map ((Opens.map r.base).map e).op
        (scalarExtensionTwistSection r η j U s) =
          scalarExtensionTwistSection r η j V t := by
    rw [← comparison_homEquiv_app, ← comparison_homEquiv_app]
    exact PresheafOfModules.naturality_apply
      ((tensorPullbackSectionAdjunction r).homEquiv _ _ (η j).hom).val e.op s |>.symm
  rw [← nat θ', ← nat θ] at hlocal
  exact congrArg Subtype.val hlocal

end AlgebraicGeometry.Proj
