/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Nakayama

/-! # Detecting functions on the punctured spectrum of a depth-two local ring

## References

* Stacks Project, Tags 0311 and 00LL, detection at associated primes and regular elements avoiding
  associated primes
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem depth_zero_of_maximal_associated
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hm : IsAssociatedPrime (IsLocalRing.maximalIdeal R) M) :
    IsLocalRing.depth (R := R) M = 0 := by
  have : Nontrivial M := by
    by_contra h
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    exact (not_isAssociatedPrime_of_subsingleton (I := IsLocalRing.maximalIdeal R)) hm
  have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [IsLocalRing.depth, Ideal.depth, ite_eq_right hM]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hxreg := ((RingTheory.Sequence.isRegular_cons_iff M x xs).mp hrs).1
    have hx : x ∈ IsLocalRing.maximalIdeal R := hmem x (by simp)
    have hunion : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
      Set.mem_iUnion.mpr ⟨IsLocalRing.maximalIdeal R, Set.mem_iUnion.mpr ⟨hm, hx⟩⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact False.elim (hunion hxreg)

/-- A function on a depth-two local affine scheme is detected by its germs away
from the closed point. -/
theorem eq_zero_of_depth_two_punctured_germs
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (a : A)
    (ha : ∀ x : Spec (.of A), x ≠ IsLocalRing.closedPoint A →
      ((Spec (.of A)).presheaf.Γgerm x).hom ((ΓSpecIso (.of A)).inv.hom a) = 0) :
    a = 0 := by
  apply (Module.injective_pi_localization_associatedPrimes A A).2
  intro p
  let x : Spec (.of A) := ⟨p.1, p.2.isPrime⟩
  have hx : x ≠ IsLocalRing.closedPoint A := by
    intro hx
    have hp : p.1 = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal hx
    have hz := depth_zero_of_maximal_associated (M := A) (hp ▸ p.2)
    rw [hz] at hdepth
    norm_num at hdepth
  have hg := ha x hx
  have halg : algebraMap A (Localization.AtPrime p.1) a = 0 := by
    have heq := RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of A) x)) a
    have hz : (Spec.stalkIso (.of A) x).inv.hom
        (algebraMap A (Localization.AtPrime p.1) a) = 0 := by
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using
        heq.trans hg
    exact (ConcreteCategory.bijective_of_isIso (Spec.stalkIso (.of A) x).inv).1
      (hz.trans (map_zero _).symm)
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.1.primeCompl
    (Localization.AtPrime p.1) a).mp halg
  exact ⟨s, s.2, by simpa only [smul_eq_mul, mul_comm] using hs⟩

end AlgebraicGeometry.Scheme
