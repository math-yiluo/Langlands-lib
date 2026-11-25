/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteFlatStalk
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatDepthTwoFiniteFormallyUnramified

/-!
# Extending finite etale covers across a regular codimension-two boundary

## References

* Stacks Project, Tag 0BMA (local purity), Tag 0EY7 (extension), and Tag 0EY6(2) (uniqueness), and
  Tag 0H2W, final paragraph (the locally Noetherian form)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem depth_two_of_regular_local (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) :
    (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
  classical
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  let rs := s.toList
  have hspan : Ideal.span {x | x ∈ rs} = m := by
    simpa [rs] using hs
  have hdim' : ringKrullDim R = (rs.length : WithBot ℕ∞) := by
    simpa [rs, hcard, m] using
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hparams : IsLocalRing.IsRegularSystemOfParameters rs := ⟨hspan, hdim'.symm⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R rs.length hdim' rs hparams).1
  have hdepth : (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, rfl⟩
      intro x hx
      change x ∈ m
      rw [← hspan]
      exact Ideal.subset_span hx
  have htwo : (2 : ℕ∞) ≤ (rs.length : ℕ∞) := by
    rw [hdim'] at hdim
    exact WithBot.coe_le_coe.mp hdim
  exact htwo.trans hdepth

/-- A finite etale cover of an open extends across a regular boundary whose
local rings have dimension at least two. -/
theorem exists_finite_etale_extension_of_regular_codimension_two_boundary
    {L Y : Scheme.{u}} [IsLocallyNoetherian L]
    (V : L.Opens)
    (hboundary : ∀ z : L, z ∉ V → IsRegularLocalRing (L.presheaf.stalk z) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk z))
    (q : Y ⟶ V.toScheme) [IsFinite q] [Etale q] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : Y ≅ (p ⁻¹ᵁ V).toScheme, e.hom ≫ (p ∣_ V) = q := by
  have hdepth : ∀ z : L, z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk z) (L.presheaf.stalk z) := by
    intro z hz
    obtain ⟨hreg, hdim⟩ := hboundary z hz
    let := hreg
    exact depth_two_of_regular_local _ hdim
  obtain ⟨E, p, hp, hE, e, he⟩ := exists_finite_extension_of_depth_two V hdepth q
  let := hp
  have : Etale (p ∣_ V) := by
    rw [← he]
    infer_instance
  have : Flat p := by
    apply Flat.of_stalkMap
    exact flat_stalk_of_regular_codimension_two_depth_two_extension V hboundary p hE
  have : FormallyUnramified p :=
    formallyUnramified_of_flat_depth_two_finite_extension V p hE
  refine ⟨E, p, hp, Etale.of_formallyUnramified_of_flat p, e.symm, ?_⟩
  rw [← he]
  simp

end AlgebraicGeometry.Scheme
