/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import all WeilConjectures.RingTheory.FlatFiberLocalDepth
import WeilConjectures.RingTheory.SerreCriterionNormal
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! # Associated-prime detection of non-normal localizations

Source: Stacks Project, Algebra, Lemma Tag 0332, proof, Cases I and II.
(blueprint: lem-weil-pbc-normal-locus-associated-prime)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

private theorem depth_le_dim (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] :
    (IsLocalRing.depth (R := A) A : WithBot ℕ∞) ≤ ringKrullDim A := by
  have hb : (⊥ : Ideal A) ∈ associatedPrimes A A := by
    apply isAssociatedPrime_iff.mpr
    refine ⟨inferInstance, 1, ?_⟩
    ext a
    simp [Submodule.mem_colon_singleton, smul_eq_mul]
  have h := IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (⊥ : Ideal A) hb
  rwa [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)] at h

private theorem normal_local_depth_bound {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (r : Ideal A) [r.IsPrime]
    (hn : IsIntegrallyClosed (Localization.AtPrime r)) :
    min (2 : ℕ∞) r.height ≤
      IsLocalRing.depth (R := Localization.AtPrime r) (Localization.AtPrime r) := by
  let C := Localization.AtPrime r
  have : IsIntegrallyClosed C := hn
  have hS : Ring.IsSerreS C 2 :=
    (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS C).mp (by
    intro s hs
    exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization
      (Localization.AtPrime s) s.primeCompl s.primeCompl_le_nonZeroDivisors⟩) |>.2
  let m := IsLocalRing.maximalIdeal C
  let e : C ≃+* Localization.AtPrime m :=
    (IsLocalization.atUnits C m.primeCompl (by
      intro x hx
      change IsUnit x
      change x ∉ IsLocalRing.maximalIdeal C at hx
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hx)).toRingEquiv
  have hmheight : m.height = r.height := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height r]
  have h := hS m
  rw [hmheight, ← RingHom.depth_eq_of_ringEquiv e] at h
  exact h

/-- A nonnormal prime of a Noetherian domain contains a nonnormal prime whose
local ring has depth at most one.

Source: Stacks Project, Algebra, Tag 0332, proof, Cases I and II.
(blueprint: lem-weil-pbc-normal-locus-associated-prime)

Proof:
1. Apply Serre's criterion to the Noetherian local domain R_p. A failure of
normality gives a prime of R_p where R1 or S2 fails. Contract it to q in R;
prime correspondence gives q ≤ p and localization of localization identifies
its local ring with R_q.
2. In the S2 case depth is less than min(2,dim R_q), so it is at most one.
A normal local domain satisfies S2, so this localization is not normal.
3. In the R1 case dimension is at most one and the local ring is not regular.
Depth is bounded by dimension (apply the associated-prime depth bound to the
zero associated prime of the domain). A normal Noetherian local domain of
dimension at most one is regular, so this localization is not normal.
Dimension zero is harmless: a zero-dimensional local domain is a field.
No principal element or principal quotient is involved in this witness. -/
private theorem exists_nonNormal_lowDepth_prime_le
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (p : PrimeSpectrum R)
    (hp : ¬ (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))) :
    ∃ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal ∧
      ¬ (IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) ∧
      IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) ≤ 1 := by
  classical
  let A := Localization.AtPrime p.asIdeal
  have hnot : ¬ (Ring.IsSerreR A 1 ∧ Ring.IsSerreS A 2) := by
    intro h
    have hall := (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS A).mpr h
    let m := IsLocalRing.maximalIdeal A
    let e : A ≃+* Localization.AtPrime m :=
      (IsLocalization.atUnits A m.primeCompl (by
        intro x hx
        change IsUnit x
        change x ∉ IsLocalRing.maximalIdeal A at hx
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hx
        )).toRingEquiv
    have hn : IsIntegrallyClosed A := (hall m).2.of_equiv e.symm
    exact hp ⟨inferInstance, hn⟩
  have hex : ∃ r : Ideal A, ∃ _ : r.IsPrime,
      ¬ (IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)) ∧
      IsLocalRing.depth (R := Localization.AtPrime r) (Localization.AtPrime r) ≤ 1 := by
    rcases not_and_or.mp hnot with hR | hS
    · unfold Ring.IsSerreR at hR
      push Not at hR
      obtain ⟨r, hr, hheight, hreg⟩ := hR
      let := hr
      refine ⟨r, hr, ?_, ?_⟩
      · intro hn
        let := hn.2
        exact hreg (IsRegularLocalRing.of_isIntegrallyClosed (Localization.AtPrime r)
          (by rw [IsLocalization.AtPrime.ringKrullDim_eq_height r]
              exact_mod_cast hheight))
      · have h := depth_le_dim (Localization.AtPrime r)
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height r] at h
        exact (WithBot.coe_le_coe.mp h).trans hheight
    · unfold Ring.IsSerreS at hS
      push Not at hS
      obtain ⟨r, hr, hdepth⟩ := hS
      let := hr
      refine ⟨r, hr, ?_, ?_⟩
      · intro hn
        exact (not_le_of_gt hdepth) (normal_local_depth_bound r hn.2)
      · have hlt : IsLocalRing.depth (R := Localization.AtPrime r)
            (Localization.AtPrime r) < 2 := hdepth.trans_le (min_le_left _ _)
        exact ENat.lt_two_iff.mp hlt
  obtain ⟨r, hr, hrn, hrd⟩ := hex
  let := hr
  let q : PrimeSpectrum R := ⟨r.comap (algebraMap R A), inferInstance⟩
  have hqp : q.asIdeal ≤ p.asIdeal :=
    ((IsLocalization.AtPrime.orderIsoOfPrime A p.asIdeal) ⟨r, hr⟩).2.2
  let e : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime r :=
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      p.asIdeal.primeCompl r).toRingEquiv
  refine ⟨q, hqp, ?_, ?_⟩
  · intro hn
    exact hrn ⟨inferInstance, hn.2.of_equiv e⟩
  · rw [RingHom.depth_eq_of_ringEquiv e]
    exact hrd

/-- Every non-normal prime lies above a non-normal associated prime of the
principal quotient.

Source: Stacks Project, Algebra, Lemma Tag 0332, proof, Cases I and II.
(blueprint: lem-weil-pbc-normal-locus-associated-prime)

Proof:
1. Localize at `p` and apply Serre's criterion. Since `R_p` is not normal,
   there is a prime `q ≤ p` such that `R_q` fails S2, or has dimension at most
   one and is not regular. Localization of localization identifies these rings.
2. In either case `R_q` is not normal. Normality of `R_f` and preservation of
   normality by localization imply `f ∈ q`. Injectivity of localization in the
   domain makes the image of `f` a nonzero element of the maximal ideal of `R_q`.
3. The depth of `R_q` is at most one: in the S2 case its depth is strictly less
   than two; in the R1 case bound depth by dimension using the associated prime
   zero of the domain. Dimension zero cannot be the nonregular case, since the
   zero-dimensional local domain is a field.
4. The depth-drop theorem for the regular element `f` gives a nonzero quotient
   `R_q/fR_q` of depth zero. Its maximal ideal is associated: otherwise the
   nonzerodivisor theorem supplies a regular element in that ideal, a regular
   sequence of length one, contradicting depth zero.
5. Identify this quotient with the localization of `R/fR` at `q`. Descent of
   associated primes along localization contracts its associated maximal ideal
   to `q`, so `q` belongs to `associatedPrimes R (R ⧸ Ideal.span {f})`.
   These are exactly the witnesses asserted, with no finite-union or topology
   argument included. -/
theorem exists_nonNormal_associatedPrime_le
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (f : R) (hf : f ≠ 0)
    (hf_normal : IsDomain (Localization.Away f) ∧
      IsIntegrallyClosed (Localization.Away f))
    (p : PrimeSpectrum R)
    (hp : ¬ (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))) :
    ∃ q : PrimeSpectrum R,
      q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span {f}) ∧
      q.asIdeal ≤ p.asIdeal ∧
      ¬ (IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) := by
  classical
  obtain ⟨q, hqp, hqn, hdepth⟩ := exists_nonNormal_lowDepth_prime_le p hp
  refine ⟨q, ?_, hqp, hqn⟩
  have hfq : f ∈ q.asIdeal := by
    by_contra hfq
    let B := Localization.Away f
    let A := Localization.AtPrime q.asIdeal
    have hsub : Submonoid.powers f ≤ q.asIdeal.primeCompl :=
      Submonoid.powers_le.mpr hfq
    let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe B A
      (Submonoid.powers f) q.asIdeal.primeCompl hsub
    have : IsScalarTower R B A :=
      IsLocalization.localization_isScalarTower_of_submonoid_le B A
        (Submonoid.powers f) q.asIdeal.primeCompl hsub
    have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap R B)) A :=
      IsLocalization.isLocalization_of_submonoid_le B A
        (Submonoid.powers f) q.asIdeal.primeCompl hsub
    have : IsDomain B := hf_normal.1
    have : IsIntegrallyClosed B := hf_normal.2
    have hM : q.asIdeal.primeCompl.map (algebraMap R B) ≤ nonZeroDivisors B := by
      rintro x ⟨r, hr, rfl⟩
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hz
      have hrzero : r = 0 :=
        (IsLocalization.injective B (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hf))) (by simpa using hz)
      exact hr (hrzero ▸ q.asIdeal.zero_mem)
    exact hqn ⟨inferInstance, isIntegrallyClosed_of_isLocalization A _ hM⟩
  let A := Localization.AtPrime q.asIdeal
  let m := IsLocalRing.maximalIdeal A
  let g : R →ₗ[R] A := Algebra.linearMap R A
  let I := Ideal.span {f}
  let J := I.localized' A q.asIdeal.primeCompl g
  let Q := A ⧸ J
  have hfmax : algebraMap R A f ∈ m :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A q.asIdeal f).mpr hfq
  have hreg : IsSMulRegular A (algebraMap R A f) := by
    have hf' := IsLocalization.nonZeroDivisors_le_comap
      (M := q.asIdeal.primeCompl) (S := A) (mem_nonZeroDivisors_iff_ne_zero.mpr hf)
    exact (isRegular_iff_mem_nonZeroDivisors.mpr hf').1.isSMulRegular
  open scoped Pointwise in
  have hJ : J = algebraMap R A f • (⊤ : Submodule A A) := by
    dsimp [J, I, g]
    rw [Submodule.localized'_span]
    simp only [Set.image_singleton, Algebra.linearMap_apply]
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨hQ, d, hd, hAdepth, hQdepth⟩ :=
    IsLocalRing.depth_quotSMulTop_of_isSMulRegular A (algebraMap R A f) hfmax hreg
  have hd1 : d = 1 := by
    have hdle : (d : ℕ∞) ≤ 1 := hAdepth ▸ hdepth
    have hdle' : d ≤ 1 := by exact_mod_cast hdle
    omega
  have hz : IsLocalRing.depth (R := A) (QuotSMulTop (algebraMap R A f) A) = 0 := by
    simpa [hd1] using hQdepth
  have : Nontrivial Q := by
    change Nontrivial (A ⧸ J)
    rw [hJ]
    exact hQ
  have hzQ : IsLocalRing.depth (R := A) Q = 0 := by
    change IsLocalRing.depth (R := A) (A ⧸ J) = 0
    rw [hJ]
    exact hz
  have hass : m ∈ associatedPrimes A Q := by
    by_contra hm
    obtain ⟨x, hx, hxreg⟩ := exists_mem_maximalIdeal_smul_injective A Q hm
    have hmem : ∀ a ∈ ([x] : List A), a ∈ IsLocalRing.maximalIdeal A :=
      by simpa using hx
    have hseq : RingTheory.Sequence.IsRegular Q [x] :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
        (RingTheory.Sequence.IsWeaklyRegular.cons hxreg
          (RingTheory.Sequence.IsWeaklyRegular.nil A (QuotSMulTop x Q)))
    have hone : (1 : ℕ∞) ≤ IsLocalRing.depth (R := A) Q := by
      unfold IsLocalRing.depth Ideal.depth
      split_ifs
      · exact le_top
      · exact le_sSup ⟨[x], hseq, hmem, by simp⟩
    rw [hzQ] at hone
    exact (by decide : ¬ (1 : ℕ∞) ≤ 0) hone
  open Module.associatedPrimes in
  have hdesc :=
    comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      q.asIdeal.primeCompl (I.toLocalizedQuotient' A q.asIdeal.primeCompl g) m hass
      ((isNoetherianRing_iff_ideal_fg R).mp inferInstance _)
  simpa [m, A, Localization.AtPrime.under_maximalIdeal] using hdesc

end AlgebraicGeometry
