import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Reducedness of principal fibres with normal local rings -/

open IsLocalRing

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- The local ring at a prime of a quotient is the quotient of the local ring at
the inverse image of that prime by the extended ideal. -/
noncomputable def localizationAtPrimeQuotientEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (q : Ideal (R ⧸ I)) [q.IsPrime] :
    let p := q.comap (Ideal.Quotient.mk I)
    Localization.AtPrime q ≃ₐ[R ⧸ I]
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  let p := q.comap (Ideal.Quotient.mk I)
  let S := Localization.AtPrime p
  have hcompl : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl :=
    q.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalization q.primeCompl (S ⧸ I.map (algebraMap R S)) := by
    rw [← hcompl]
    infer_instance
  exact IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _

private theorem maximalIdeal_isPrincipal_of_colon {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    {a b : R} (ha : a ≠ 0)
    (hcolon : ∀ t : R, t ∈ maximalIdeal R ↔ t * b ∈ Ideal.span {a}) :
    (maximalIdeal R).IsPrincipal := by
  have hb : b ∉ Ideal.span {a} := fun h =>
    (maximalIdeal R).ne_top_iff_one.mp (maximalIdeal.isMaximal R).ne_top
      ((hcolon 1).mpr (by simpa using h))
  have hb₀ : b ≠ 0 := fun h => hb (h ▸ (Ideal.span {a}).zero_mem)
  let K := FractionRing R
  let f := algebraMap R K
  let x : K := f b / f a
  have hf : Function.Injective f := IsFractionRing.injective R K
  have haK : f a ≠ 0 := (map_ne_zero_iff f hf).mpr ha
  have hx : x ≠ 0 := div_ne_zero ((map_ne_zero_iff f hf).mpr hb₀) haK
  let M : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R : Submodule R R)
  have hmul (r : R) (hr : r ∈ maximalIdeal R) : ∃ t : R, x * f r = f t := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ((hcolon r).mp hr)
    refine ⟨t, ?_⟩
    change (f b / f a) * f r = f t
    rw [div_mul_eq_mul_div, div_eq_iff haK, ← map_mul, ← map_mul, mul_comm b r, ht]
  by_cases hstable : ∀ y ∈ M, x * y ∈ M
  · have haM : f a ∈ M :=
      ⟨a, (hcolon a).mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right a b)), rfl⟩
    have hM : M ≠ ⊥ := M.ne_bot_iff.mpr ⟨f a, haM, haK⟩
    have hfg : M.FG := (IsNoetherian.noetherian (maximalIdeal R : Submodule R R)).map _
    have hxint : IsIntegral R x := isIntegral_of_smul_mem_submodule M hM hfg x hstable
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := R) hxint
    exact (hb (Ideal.mem_span_singleton'.mpr ⟨t, hf (by
      rw [map_mul, ht, div_mul_cancel₀ _ haK])⟩)).elim
  · push Not at hstable
    obtain ⟨_, ⟨r, hr, rfl⟩, hnot⟩ := hstable
    obtain ⟨t, ht⟩ := hmul r hr
    have htunit : IsUnit t := by
      rw [← notMem_maximalIdeal]
      exact fun htmem => hnot ⟨t, htmem, ht.symm⟩
    obtain ⟨u, rfl⟩ := htunit
    let r₀ := (↑u⁻¹ : R) * r
    have hr₀ : r₀ ∈ maximalIdeal R := (maximalIdeal R).mul_mem_left _ hr
    have hx₀ : x * f r₀ = 1 := by
      rw [show r₀ = (↑u⁻¹ : R) * r from rfl, map_mul, mul_left_comm, ht, ← map_mul]
      simp
    refine ⟨⟨r₀, le_antisymm ?_ ((maximalIdeal R).span_singleton_le_iff_mem.mpr hr₀)⟩⟩
    intro y hy
    obtain ⟨v, hv⟩ := hmul y hy
    refine Ideal.mem_span_singleton'.mpr ⟨v, hf (mul_left_cancel₀ hx ?_)⟩
    rw [map_mul, mul_left_comm, hx₀, mul_one, hv]

section

variable {R : Type*} [CommRing R]

private theorem mem_colon_quotient_iff {I : Ideal R} {b t : R} :
    t ∈ (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I b} ↔ t * b ∈ I := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]

end

/-- In a Noetherian ring with normal domain localizations at prime ideals, a quotient
by a regular element is reduced if it is reduced at the primes minimal over that element. -/
theorem isReduced_quotient_span_singleton_of_minimalPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {a : R} (ha : a ∈ nonZeroDivisors R)
    (hNormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hReduced : ∀ (p : Ideal R) [p.IsPrime], (Ideal.span {a}).IsMinimalPrime p →
      IsReduced (Localization.AtPrime p ⧸ (Ideal.span {a}).map
        (algebraMap R (Localization.AtPrime p)))) :
    IsReduced (R ⧸ Ideal.span {a}) := by
  let I := Ideal.span {a}
  constructor
  intro z hz
  by_contra hne
  obtain ⟨p, hp, hzle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R z hne
  have hpPrime : p.IsPrime := hp.isPrime
  obtain ⟨_, y, hy⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hb (t : R) : t ∈ p ↔ t * b ∈ I := by rw [hy, mem_colon_quotient_iff]
  have hIp : I ≤ p := by
    rw [Ideal.span_singleton_le_iff_mem, hb]
    exact I.mul_mem_right b (Ideal.mem_span_singleton_self a)
  let S := Localization.AtPrime p
  let f := algebraMap R S
  obtain ⟨hDomain, hClosed⟩ := hNormal p
  have haS : f a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
    (IsLocalization.map_nonZeroDivisors_le p.primeCompl S ⟨a, ha, rfl⟩)
  have hcolon (t : S) : t ∈ maximalIdeal S ↔ t * f b ∈ Ideal.span {f a} := by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl t
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Set.image_singleton (f := f),
      ← Ideal.map_span, ← IsLocalization.mk'_one (M := p.primeCompl) S b,
      ← IsLocalization.mk'_mul, mul_one]
    rw [IsLocalization.mk'_mem_map_algebraMap_iff p.primeCompl S p r s,
      IsLocalization.mk'_mem_map_algebraMap_iff p.primeCompl S I (r * b) s]
    simp only [hb, mul_assoc]
  have hPrincipal : (maximalIdeal S).IsPrincipal := maximalIdeal_isPrincipal_of_colon haS hcolon
  have hPID : IsPrincipalIdealRing S :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 5 1).mp hPrincipal
  have hpmin : I.IsMinimalPrime p := by
    refine ⟨⟨hpPrime, hIp⟩, ?_⟩
    intro q hq hqp
    have hqPrime : q.IsPrime := hq.1
    have hqS : (q.map f).IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime p hqp
    have haq : a ∈ q := hq.2 (Ideal.mem_span_singleton_self a)
    have hqne : q.map f ≠ ⊥ := by
      intro h
      have hm := Ideal.mem_map_of_mem f haq
      rw [h, Ideal.mem_bot] at hm
      exact haS hm
    have hqmax := eq_maximalIdeal (hqS.isMaximal hqne)
    rw [← Ideal.under_map_of_isLocalizationAtPrime p (S := S) hqp,
      hqmax, Localization.AtPrime.under_maximalIdeal]
  have hred := hReduced p hpmin
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  have hcn : c ^ n ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow] using hn)
  have hc : f c ∈ I.map f := Ideal.Quotient.eq_zero_iff_mem.mp <|
    hred.eq_zero _ ⟨n, by
      rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem f hcn⟩
  obtain ⟨s, hs, hsc⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S I c).mp hc
  exact hs (hzle (mem_colon_quotient_iff.mpr hsc))

/-- A regular principal quotient of a Noetherian ring with normal domain localizations
is reduced if its own local rings at all minimal primes are reduced. -/
theorem isReduced_principal_quotient_of_isReduced_at_minimalPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {a : R} (ha : a ∈ nonZeroDivisors R)
    (hNormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hReduced : ∀ (q : Ideal (R ⧸ Ideal.span {a})) [q.IsPrime],
      IsMinimalPrime q → IsReduced (Localization.AtPrime q)) :
    IsReduced (R ⧸ Ideal.span {a}) := by
  refine isReduced_quotient_span_singleton_of_minimalPrimes ha hNormal (fun p _ hp ↦ ?_)
  change p ∈ (Ideal.span {a}).minimalPrimes at hp
  rw [Ideal.minimalPrimes_eq_comap] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have : q.IsPrime := hq.isPrime
  have : IsReduced (Localization.AtPrime q) := hReduced q hq
  let e := localizationAtPrimeQuotientEquiv (Ideal.span {a}) q
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
