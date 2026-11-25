/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Incomparability for integral morphisms

Inside a fibre of an integral morphism of schemes there are no nontrivial specializations
(`AlgebraicGeometry.Scheme.Hom.eq_of_specializes_of_apply_eq_of_isIntegralHom`): affine locally
this is incomparability for integral ring extensions (`Ideal.IsIntegral.comap_lt_comap`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Inside a fibre of an integral morphism there are no nontrivial specializations. -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq_of_isIntegralHom (f : X ⟶ Y) [IsIntegralHom f]
    {x x' : X} (h : x ⤳ x') (hx : f x = f x') : x = x' := by
  obtain ⟨V, hV, hxV⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ f x' ∈ V := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show f x' ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  have hx'U : x' ∈ f ⁻¹ᵁ V := hxV
  have hxU : x ∈ f ⁻¹ᵁ V := h.mem_open (f ⁻¹ᵁ V).isOpen hx'U
  have : IsAffine V := hV
  have : IsAffine (f ⁻¹ᵁ V) := hV.preimage f
  set g := f ∣_ V
  have hg : IsIntegralHom g := inferInstance
  -- the points as primes of the rings of sections
  let a : f ⁻¹ᵁ V := ⟨x, hxU⟩
  let a' : f ⁻¹ᵁ V := ⟨x', hx'U⟩
  have hspec : a ⤳ a' := (Topology.IsInducing.subtypeVal.specializes_iff).1 h
  have hga : g a = g a' := Subtype.ext (by simpa [g] using hx)
  suffices a = a' from congrArg Subtype.val this
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)] at hg
  let φ := g.appTop
  have hφ : φ.hom.IsIntegral := hg.2
  let := φ.hom.toAlgebra
  have : Algebra.IsIntegral Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := ⟨hφ⟩
  set P := (f ⁻¹ᵁ V).toScheme.isoSpec.hom a
  set P' := (f ⁻¹ᵁ V).toScheme.isoSpec.hom a'
  have hPP' : P ⤳ P' := hspec.map (f ⁻¹ᵁ V).toScheme.isoSpec.hom.continuous
  have hcomap : (Spec.map φ) P = (Spec.map φ) P' := by
    simp only [P, P', ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, φ]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hga]
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').2 hPP'
  have hPeq : P = P' := by
    by_contra hne
    have hlt : P.asIdeal < P'.asIdeal :=
      lt_of_le_of_ne hle fun h ↦ hne (PrimeSpectrum.ext h)
    have := Ideal.IsIntegral.under_lt_under (R := Γ(V, ⊤)) hlt
    exact this.ne (congrArg PrimeSpectrum.asIdeal hcomap)
  exact (f ⁻¹ᵁ V).toScheme.isoSpec.hom.homeomorph.injective hPeq

end AlgebraicGeometry
