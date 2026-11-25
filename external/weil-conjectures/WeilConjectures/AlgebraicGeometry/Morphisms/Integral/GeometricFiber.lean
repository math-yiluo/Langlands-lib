/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNeighborhood

/-!
# The geometric fibre of an integral morphism

Let `f : X ⟶ Y` be an integral morphism and `y : Spec Ω ⟶ Y` a geometric point with `Ω`
algebraically closed. Every point of the scheme-theoretic fibre of `f` over `y` is the image of
a geometric point of `X` over `y`
(`AlgebraicGeometry.Scheme.Hom.GeometricFiber.exists_apply_default_eq_of_isIntegralHom`), and a
closed subset of `U ×_Y X` avoiding the points `(u, t)` disappears over a smaller pointed étale
neighbourhood of `y` (`AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot_of_isIntegralHom`).
These are the integral versions of the corresponding statements for finite morphisms, with the
same proofs: only lying over and the closedness of integral morphisms are used.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite RingHom

namespace AlgebraicGeometry.Scheme.Hom

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

attribute [local instance] affineAlgebra in
/-- **Every point of the fibre of an integral morphism over a geometric point `y` with values in
an algebraically closed field is the image of a geometric point over `y`.** -/
lemma GeometricFiber.exists_apply_default_eq_of_isIntegralHom [IsIntegralHom f] [IsAlgClosed Ω]
    (x : X) (hx : f x = y default) :
    ∃ t : GeometricFiber f y, t.1 default = x := by
  obtain ⟨Y₀, hY₀, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y default) (U := ⊤) trivial
  have : Algebra.IsIntegral Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) :=
    ⟨fun b ↦ (f.isIntegral_app Y₀ hY₀) b⟩
  have hx₀ : x ∈ Set.range (hY₀.preimage f).fromSpec.base := by
    rw [(hY₀.preimage f).range_fromSpec]
    change f x ∈ Y₀
    rw [hx]
    exact hy
  obtain ⟨𝔮, rfl⟩ := hx₀
  have h𝔮 : 𝔮.asIdeal.LiesOver (RingHom.ker (affinePoint y hY₀ hy)) := ⟨by
    have h₁ := congrArg (hY₀.fromSpec.base) (show Spec.map (f.app Y₀) 𝔮 =
      Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) default from ?_)
    · rw [Spec.map_default_eq, Spec.map_apply] at h₁
      have := hY₀.fromSpec.isOpenEmbedding.injective h₁
      exact congrArg PrimeSpectrum.asIdeal this.symm
    · apply hY₀.fromSpec.isOpenEmbedding.injective
      change (Spec.map (f.app Y₀) ≫ hY₀.fromSpec) 𝔮 =
        (Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) ≫ hY₀.fromSpec) default
      rw [SpecMap_app_fromSpec f hY₀, SpecMap_affinePoint_fromSpec, Scheme.Hom.comp_apply]
      exact hx⟩
  obtain ⟨t, ht⟩ := PointsOver.exists_ker_eq (φ := affinePoint y hY₀ hy) 𝔮.asIdeal
  refine ⟨(geometricFiberEquivPointsOver f y hY₀ hy).symm t, ?_⟩
  rw [geometricFiberEquivPointsOver_symm_apply_default]
  congr 1
  exact PrimeSpectrum.ext ht

end Fibre

section Shrink

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y} [IsIntegralHom f]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Shrinking away from a closed subset without geometric points**, for an integral
morphism. -/
theorem exists_hom_preimage_eq_bot_of_isIntegralHom (c : Nbhd y)
    (C : Set (pullback c.1.hom f : Scheme.{u}))
    (hC : IsClosed C) (h : ∀ t : GeometricFiber f y, basePt f c t default ∉ C) :
    ∃ (c' : Nbhd y) (g : c' ⟶ c), (f.Etale.map g.val).left.base ⁻¹' C = ∅ := by
  obtain @⟨U, u⟩ := c
  set Z : Set U.left := (pullback.fst U.hom f).base '' C with hZ
  have hZc : IsClosed Z := (pullback.fst U.hom f).isClosedMap C hC
  have hu : u.left (default : Spec (.of Ω)) ∉ Z := by
    rintro ⟨z, hzC, hz⟩
    obtain ⟨z', hz'⟩ := GeometricFiber.exists_apply_default_eq_of_isIntegralHom
      (pullback.fst U.hom f) u.left z hz
    refine h ⟨z'.1 ≫ pullback.snd U.hom f, ?_⟩ ?_
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc, z'.2]
      exact CategoryTheory.Over.w u
    · rw [basePt_eq_of_comp_fst_eq f (Functor.elementsMk _ U u) z'.1 z'.2, hz']
      exact hzC
  let U' : U.left.Opens := ⟨Zᶜ, hZc.isOpen_compl⟩
  have hrange : Set.range u.left.base ⊆ Set.range U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
    exact hu
  set u' := IsOpenImmersion.lift U'.ι u.left hrange with hu'
  have hu'ι : u' ≫ U'.ι = u.left := IsOpenImmersion.lift_fac _ _ _
  let θ : Scheme.Etale.mk (U'.ι ≫ U.hom) ⟶ U := MorphismProperty.Over.homMk U'.ι rfl
  refine ⟨Functor.elementsMk _ (Scheme.Etale.mk (U'.ι ≫ U.hom))
    (CategoryTheory.Over.homMk u' ?_),
    Functor.Elements.homMk θ ?_, ?_⟩
  · change u' ≫ U'.ι ≫ U.hom = y
    rw [← Category.assoc, hu'ι]
    exact CategoryTheory.Over.w u
  · exact CategoryTheory.Over.OverMorphism.ext hu'ι
  · rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    have h₁ : (pullback.fst U.hom f) ((f.Etale.map θ).left w) =
        U'.ι ((pullback.fst (Scheme.Etale.mk (U'.ι ≫ U.hom)).hom f) w) :=
      congrArg (fun m ↦ m.base w) (Hom.etale_map_left_comp_fst f θ)
    have h₂ : (pullback.fst U.hom f) ((f.Etale.map θ).left w) ∈ Z := ⟨_, hw, rfl⟩
    rw [h₁] at h₂
    exact ((Scheme.Opens.range_ι U').subset (Set.mem_range_self _)) h₂

end Shrink

end AlgebraicGeometry.Scheme.Hom
