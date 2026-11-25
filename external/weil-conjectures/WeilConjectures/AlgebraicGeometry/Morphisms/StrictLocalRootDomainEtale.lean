/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The strict local root algebra is a domain with etale puncture

## References

* Stacks Project, Tags 0EYG and 09EV
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The root algebra is a domain and its puncture is etale. -/
theorem strict_local_root_domain_etale
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen (algebraMap H C h)
    IsDomain C ∧ Etale (V.ι ≫ q) := by
  intro C q V
  classical
  let P := (Polynomial.X : Polynomial H) ^ n - Polynomial.C h
  let t := AdjoinRoot.root P
  have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C h hn.1.ne'
  have : Module.Finite H C := hmonic.finite_adjoinRoot
  have hpow : t ^ n = algebraMap H C h := by
    simpa [t, P, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root P
  let k := IsLocalRing.ResidueField H
  let r := IsLocalRing.residue H
  have hrh : r h = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hhm
  let ε : C →+* k := AdjoinRoot.lift r 0 (by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, zero_pow hn.1.ne', zero_sub, neg_eq_zero]
    exact hrh)
  have hε : Function.Surjective ε := by
    intro y
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := H) y
    exact ⟨algebraMap H C x, (AdjoinRoot.lift_of _).trans hx⟩
  have hmax : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective ε hε
  have huniq (M : Ideal C) [M.IsMaximal] : M = RingHom.ker ε := by
    have hcomap : M.comap (algebraMap H C) = IsLocalRing.maximalIdeal H :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal M)
    have htm : t ∈ M := by
      apply Ideal.IsPrime.mem_of_pow_mem (inferInstance : M.IsPrime) n
      rw [hpow]
      exact show h ∈ M.comap (algebraMap H C) from hcomap ▸ hhm
    have heval (p : Polynomial H) :
        Ideal.Quotient.mk M (AdjoinRoot.mk P p) =
          Ideal.Quotient.mk M (algebraMap H C (p.eval 0)) := by
      have hx : Ideal.Quotient.mk M t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr htm
      have he := Polynomial.eval₂_at_apply
        ((Ideal.Quotient.mk M).comp (algebraMap H C)) 0 (p := p)
      rw [← AdjoinRoot.aeval_eq]
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      change Polynomial.eval₂ ((Ideal.Quotient.mk M).comp (algebraMap H C))
        (Ideal.Quotient.mk M t) p = _
      rw [hx]
      simpa only [map_zero, RingHom.comp_apply] using he
    ext x
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      rw [← Ideal.Quotient.eq_zero_iff_mem, heval, Ideal.Quotient.eq_zero_iff_mem]
      change (p.eval 0 ∈ M.comap (algebraMap H C)) ↔ ε (AdjoinRoot.mk P p) = 0
      rw [hcomap]
      rw [AdjoinRoot.lift_mk]
      have he : p.eval₂ r 0 = r (p.eval 0) := by
        simpa only [map_zero] using Polynomial.eval₂_at_apply r 0 (p := p)
      rw [he]
      exact Ideal.Quotient.eq_zero_iff_mem.symm
  have : IsLocalRing C := IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker ε, hmax, fun M hM => @huniq M hM⟩
  have htmax : t ∈ IsLocalRing.maximalIdeal C := by
    rw [← IsLocalRing.eq_maximalIdeal hmax]
    change ε t = 0
    exact AdjoinRoot.lift_root _
  have : IsRegularRing (H ⧸ Ideal.span {h}) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (H ⧸ Ideal.span {h}))).2
  have : IsRegularLocalRing (Localization.AtPrime (IsLocalRing.maximalIdeal C)) :=
    AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem H h hh n hn.1
      (IsLocalRing.maximalIdeal C) htmax
  let e := IsLocalization.atUnits C (IsLocalRing.maximalIdeal C).primeCompl
    (S := Localization.AtPrime (IsLocalRing.maximalIdeal C)) (by
      intro x hx
      exact IsLocalRing.notMem_maximalIdeal.mp hx)
  have : IsRegularLocalRing C := IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  exact ⟨inferInstance, root_split_away_cover_etale (CommRingCat.of H) h n hn⟩


end AlgebraicGeometry.Scheme
