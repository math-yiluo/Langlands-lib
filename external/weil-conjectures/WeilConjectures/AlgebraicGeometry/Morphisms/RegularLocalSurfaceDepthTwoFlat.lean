/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.Depth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.RingTheory.MiracleFlatness
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-!
# Flatness of a depth-two finite model over a regular local surface

## References

* Stacks Project, Tag 0BMA, dimension-two paragraph, and Tag 00R4
* Stacks Project, Tag 0BMA, dimension-two paragraph, using miracle flatness (00R4)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem dimension_le_of_quasiFinite {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.QuasiFinite) :
    ringKrullDim S ≤ ringKrullDim R := by
  algebraize [φ]
  have : Algebra.QuasiFinite R S := hφ
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap φ)
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  have h := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
    p.asIdeal q.asIdeal hpq.le (congrArg PrimeSpectrum.asIdeal heq)
  exact hpq.ne (PrimeSpectrum.ext h)

private theorem fibre_dimension_zero {R S : Type u}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hφ : φ.QuasiFinite) :
    ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ) = 0 := by
  algebraize [φ]
  have : Algebra.QuasiFinite R S := hφ
  let I := (IsLocalRing.maximalIdeal R).map φ
  have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top φ).ne
  let Q := S ⧸ I
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hunder (p : Ideal Q) [p.IsPrime] : p.under R = IsLocalRing.maximalIdeal R := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top' (I := p.under R))
    intro x hx
    change algebraMap R Q x ∈ p
    have hxI : φ x ∈ I := Ideal.mem_map_of_mem φ hx
    have hzero : algebraMap R Q x = 0 := by
      change Ideal.Quotient.mk I (φ x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
    rw [hzero]
    exact p.zero_mem
  have : Ring.KrullDimLE 0 Q := by
    apply Ring.krullDimLE_zero_iff.mpr
    intro p hp
    have := hp
    have heq : p = IsLocalRing.maximalIdeal Q :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) p (IsLocalRing.maximalIdeal Q)
        (IsLocalRing.le_maximalIdeal hp.ne_top) ((hunder p).trans (hunder _).symm)
    rw [heq]
    infer_instance
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- A supplied finite extension with boundary depth two is flat over a regular local surface. -/
theorem flat_of_regular_local_surface_depth_two
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {F : Scheme.{u}} (r : F ⟶ Spec (.of A)) [IsFinite r] [Etale (r ∣_ U)]
    (hsource : ∀ x : F, r x ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk x) (F.presheaf.stalk x)) :
    Flat r := by
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian r
  apply Flat.of_stalkMap
  intro x
  by_cases hx : r x ∈ U
  · let xU : (r ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap r U xU)).mp (Flat.stalkMap (r ∣_ U) xU)
  · have hclosed : r x = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hx ((hU (r x)).mpr hne)
    let R := (Spec (.of A)).presheaf.stalk (r x)
    let S := F.presheaf.stalk x
    let φ := (r.stalkMap x).hom
    let e : R ≅ .of A :=
      eqToIso (congrArg (fun z ↦ (Spec (.of A)).presheaf.stalk z) hclosed) ≪≫
        stalkClosedPointIso (.of A)
    have : IsRegularLocalRing R :=
      IsRegularLocalRing.of_ringEquiv e.commRingCatIsoToRingEquiv.symm
    have hdimR : ringKrullDim R = 2 := by
      rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv, hdim]
    have hqf : φ.QuasiFinite := r.quasiFiniteAt x
    have hdimS : ringKrullDim S = 2 := by
      apply le_antisymm
      · exact (dimension_le_of_quasiFinite φ hqf).trans_eq hdimR
      · have hlow := IsLocalRing.depth_le_supportDim (R := S) S
        rw [Module.supportDim_self_eq_ringKrullDim] at hlow
        exact (WithBot.coe_le_coe.mpr (hsource x hx)).trans hlow
    apply RingHom.flat_of_regular_of_depth_ge φ 2 hdimS (hsource x hx)
    rw [hdimS, hdimR, fibre_dimension_zero φ hqf, add_zero]

end AlgebraicGeometry.Scheme
