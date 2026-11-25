/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularLocalSurfaceDepthTwoFlat

/-!
# A finite flat model in regular local dimension two

## References

* Stacks Project, Tag 0BMA, dimension-two paragraph
* Stacks Project, Tag 0BMA, dimension-two case, and Tag 0BM9
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

/-- A punctured finite etale cover has a finite flat model with depth-two boundary stalks. -/
theorem exists_finite_flat_model_of_regular_local_dimension_two
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q] :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsLocallyNoetherian F ∧
      IsFinite r ∧ Flat r ∧
      (∀ x : F, x ∉ r ⁻¹ᵁ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk x) (F.presheaf.stalk x)) ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by
  have hboundary : ∀ z : Spec (.of A), z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (.of A)).presheaf.stalk z) ((Spec (.of A)).presheaf.stalk z) := by
    intro z hz
    have hzclosed : z = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hz ((hU z).mpr hne)
    subst z
    let e := (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv
    have : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
        (IsLocalRing.closedPoint A)) := IsRegularLocalRing.of_ringEquiv e.symm
    apply depth_two_of_regular_local
    rw [ringKrullDim_eq_of_ringEquiv e, hdim]
  obtain ⟨F, r, hfin, hsource, e, he⟩ :=
    exists_finite_extension_of_depth_two U hboundary q
  have : IsFinite r := hfin
  have : Etale (r ∣_ U) := by
    rw [← he]
    infer_instance
  have hflat : Flat r :=
    flat_of_regular_local_surface_depth_two A hdim U hU r hsource
  have hloc : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian r
  refine ⟨F, r, hloc, hfin, hflat, hsource, e.symm, ?_⟩
  rw [← he]
  simp

end AlgebraicGeometry.Scheme
