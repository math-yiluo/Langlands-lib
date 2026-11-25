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
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity
import WeilConjectures.AlgebraicGeometry.Morphisms.LocalPurityDepthTwoFiniteFlatStalk
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatDepthTwoFiniteFormallyUnramified

/-!
# Finite etale model across a regular codimension-two boundary

## References

* Stacks Project, Tags 0BMA, 0EY7, and 0EY6(2)
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

/-- A finite etale restriction extends across a regular codimension-two boundary. -/
theorem exists_finite_etale_depth_two_model
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hboundary : ∀ y : L, y ∉ V → IsRegularLocalRing (L.presheaf.stalk y) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk y))
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)] :
    ∃ (F : Scheme.{u}) (r : F ⟶ L), IsFinite r ∧ Etale r ∧
      (∀ z : F, r z ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ (r ⁻¹ᵁ V).toScheme,
        e.hom ≫ r ∣_ V = p ∣_ V := by
  have hdepth : ∀ y : L, y ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y) := by
    intro y hy
    obtain ⟨hreg, hdim⟩ := hboundary y hy
    let := hreg
    exact depth_two_of_regular_local _ hdim
  obtain ⟨F, r, hfin, hsource, e, he⟩ :=
    exists_finite_extension_of_depth_two V hdepth (p ∣_ V)
  let := hfin
  have : Etale (r ∣_ V) := by
    rw [← he]
    infer_instance
  have : Flat r := by
    refine flat_of_local_purity_depth_two_finite_extension V hdepth ?_ r hsource
    intro y hy U hU Z q hq hqe
    obtain ⟨hreg, hdim⟩ := hboundary y hy
    let := hreg
    let := hq
    let := hqe
    exact exists_finite_etale_extension_of_regular_local_punctured_spectrum
      (L.presheaf.stalk y) hdim U hU q
  have : FormallyUnramified r :=
    formallyUnramified_of_flat_depth_two_finite_extension V r hsource
  refine ⟨F, r, hfin, Etale.of_formallyUnramified_of_flat r, hsource, e.symm, ?_⟩
  rw [← he]
  simp

end AlgebraicGeometry.Scheme
