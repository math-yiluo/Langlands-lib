/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularLocalDimensionTwoPuncturedFlatModel
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthThreePuncturedEtaleLifting

/-!
# Purity for the punctured spectrum of a regular local ring

## References

* Stacks Project, Tag 0BMA, assertion (1)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem extension_by_dimension (d : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
      ringKrullDim A = (d : WithBot ℕ∞) → 2 ≤ d →
      ∀ (U : (Spec (.of A)).Opens),
        (∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A) →
        ∀ {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q],
          ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Etale r ∧
            ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A _ _ hd htwo U hU Y q _ _
    by_cases hd2 : d = 2
    · obtain ⟨F, r, hF, hfinite, hflat, hboundary, e, he⟩ :=
        exists_finite_flat_model_of_regular_local_dimension_two A
          (by simpa [hd2] using hd) U hU q
      have : IsFinite r := hfinite
      have : Flat r := hflat
      have : IsLocallyNoetherian F := hF
      have : Etale (r ∣_ U) := by
        rw [← MorphismProperty.cancel_left_of_respectsIso @Etale e.hom, he]
        infer_instance
      have het : Etale ((r ⁻¹ᵁ U).ι ≫ r) := by
        rw [← morphismRestrict_ι]
        infer_instance
      exact ⟨F, r, hfinite,
        etale_of_flat_quasiFinite_depth_two_boundary r (r ⁻¹ᵁ U) het hboundary, e, he⟩
    have hthree : 3 ≤ d := by omega
    -- A minimal generating list gives both depth and a regular quotient.
    let m := IsLocalRing.maximalIdeal A
    obtain ⟨s, hcard, hspan⟩ :=
      (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
    let rs := s.toList
    have hspan' : Ideal.span {x | x ∈ rs} = m := by simpa [rs] using hspan
    have hlen : rs.length = d := by
      have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
      rw [hd] at hrank
      have hm : m.spanFinrank = d := by exact_mod_cast hrank
      simp [rs, hcard, hm]
    have hrs : IsLocalRing.IsRegularSystemOfParameters rs :=
      ⟨hspan', by simpa [hlen] using hd.symm⟩
    have hreg := IsRegularLocalRing.isRegular_and_quotients_of_generators A d hd rs hrs
    have hmem : ∀ x ∈ rs, x ∈ m := by
      intro x hx
      rw [← hspan']
      exact Ideal.subset_span hx
    have hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
      have hddepth : (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
        unfold IsLocalRing.depth Ideal.depth
        split_ifs
        · exact le_top
        · exact le_sSup ⟨rs, hreg.1, hmem, rfl⟩
      have hcast : (3 : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hthree
      exact hcast.trans (hlen ▸ hddepth)
    obtain ⟨f, fs, hcons⟩ : ∃ f fs, rs = f :: fs := by
      cases hrs' : rs with
      | nil => simp [hrs'] at hlen; omega
      | cons f fs => exact ⟨f, fs, rfl⟩
    have hf : f ∈ IsLocalRing.maximalIdeal A := hmem f (by simp [hcons])
    have hquotient := hreg.2.1 1 (by omega)
    have hI : Ideal.ofList (rs.take 1) = Ideal.span {f} := by
      simp [hcons]
    rw [hI] at hquotient
    let B := A ⧸ Ideal.span {f}
    have : IsRegularLocalRing B := hquotient.1
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {f})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let i : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let V := i ⁻¹ᵁ U
    have hV : ∀ x : Spec (.of B), x ∈ V ↔ x ≠ IsLocalRing.closedPoint B := by
      intro x
      change i x ∈ U ↔ x ≠ IsLocalRing.closedPoint B
      rw [hU]
      have hinj : Function.Injective i :=
        PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      have hclosed : i (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
        IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (Ideal.span {f}))
      rw [← hclosed, hinj.ne_iff]
    have hBdim : ringKrullDim B = ((d - 1 : ℕ) : WithBot ℕ∞) := hquotient.2
    have hsmall := ih (d - 1) (by omega) B hBdim (by omega) V hV
      (Limits.pullback.snd q (i ∣_ U))
    exact exists_finite_etale_extension_of_depth_three_of_quotient_extension
      A f hf hdepth U hU q hsmall

/-- Finite etale covers of the punctured spectrum of a regular local ring of dimension
at least two extend to the whole local spectrum. -/
theorem exists_finite_etale_extension_of_regular_local_punctured_spectrum
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q] :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Etale r ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by
  let d := (IsLocalRing.maximalIdeal A).spanFinrank
  have hd : ringKrullDim A = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have htwo : 2 ≤ d := by rw [hd] at hdim; exact_mod_cast hdim
  exact extension_by_dimension d A hd htwo U hU q

end AlgebraicGeometry.Scheme
