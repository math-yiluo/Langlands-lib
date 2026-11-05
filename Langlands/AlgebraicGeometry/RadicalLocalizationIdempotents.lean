import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Ring

/-! # Extending idempotents across a reduced principal divisor -/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry

open Topology

/-- Every idempotent extends uniquely across a regular element generating a radical ideal. -/
theorem existsUnique_idempotent_of_away_radical
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical) (e : S) (he : IsIdempotentElem e) :
    ∃! a : A, IsIdempotentElem a ∧ algebraMap A S a = e := by
  have hinj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S (Submonoid.powers_le.mpr ht)
  have hdenom : ∀ n : ℕ, ∀ a : A,
      e * algebraMap A S t ^ n = algebraMap A S a →
        ∃ b : A, algebraMap A S b = e := by
    intro n
    induction n with
    | zero =>
      intro a ha
      exact ⟨a, by simpa using ha.symm⟩
    | succ n ih =>
      intro a ha
      have hsq : a ^ 2 = t ^ (n + 1) * a := by
        apply hinj
        simp only [map_pow, map_mul]
        rw [← ha]
        calc
          (e * algebraMap A S t ^ (n + 1)) ^ 2 =
              (e * e) * (algebraMap A S t ^ (n + 1) *
                algebraMap A S t ^ (n + 1)) := by ring
          _ = algebraMap A S t ^ (n + 1) *
              (e * algebraMap A S t ^ (n + 1)) := by rw [he.eq]; ring
      have hamem : a ∈ Ideal.span {t} := by
        apply hrad
        refine ⟨2, ?_⟩
        rw [hsq, Ideal.mem_span_singleton]
        exact ⟨t ^ n * a, by ring⟩
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hamem
      apply ih b
      apply (IsLocalization.Away.algebraMap_isUnit t).mul_right_cancel
      calc
        (e * algebraMap A S t ^ n) * algebraMap A S t =
            e * algebraMap A S t ^ (n + 1) := by rw [pow_succ, mul_assoc]
        _ = algebraMap A S a := ha
        _ = algebraMap A S b * algebraMap A S t := by rw [hb, map_mul, mul_comm]
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj t e
  obtain ⟨b, hb⟩ := hdenom n a ha
  refine ⟨b, ⟨?_, hb⟩, ?_⟩
  · apply hinj
    simpa only [map_mul, hb] using he.eq
  · intro c hc
    exact hinj (hc.2.trans hb.symm)

/-- The quotient-reduced form of extension of idempotents over a regular principal divisor. -/
theorem existsUnique_idempotent_of_away_quotient_reduced
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span {t})] (e : S) (he : IsIdempotentElem e) :
    ∃! a : A, IsIdempotentElem a ∧ algebraMap A S a = e :=
  existsUnique_idempotent_of_away_radical t ht
    ((Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance) e he

/-- Localization at a regular element with radical principal ideal induces an equivalence
on the actual sets of idempotents. -/
def idempotentEquivOfAwayRadical
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical) :
    {a : A // IsIdempotentElem a} ≃ {e : S // IsIdempotentElem e} :=
  Equiv.ofBijective
    (fun a => ⟨algebraMap A S a, by
      change algebraMap A S a * algebraMap A S a = algebraMap A S a
      rw [← map_mul, a.2.eq]⟩)
    ⟨fun a b h => Subtype.ext
        (IsLocalization.injective S (Submonoid.powers_le.mpr ht) (congrArg Subtype.val h)),
      fun e => by
        obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
          existsUnique_idempotent_of_away_radical (S := S) t ht hrad e.1 e.2
        exact ⟨⟨a, ha⟩, Subtype.ext hae⟩⟩

@[simp]
theorem idempotentEquivOfAwayRadical_apply
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical) (a : {a : A // IsIdempotentElem a}) :
    (idempotentEquivOfAwayRadical (S := S) t ht hrad a).1 = algebraMap A S a :=
  rfl

/-- Every clopen of the localization spectrum extends to a clopen of the original spectrum. -/
theorem exists_clopen_of_away_radical
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical) {s : Set (PrimeSpectrum S)} (hs : IsClopen s) :
    ∃ z : Set (PrimeSpectrum A), IsClopen z ∧
      (PrimeSpectrum.comap (algebraMap A S)) ⁻¹' z = s := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  obtain ⟨a, ⟨ha, hae⟩, -⟩ := existsUnique_idempotent_of_away_radical t ht hrad e he
  refine ⟨PrimeSpectrum.basicOpen a, PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩, ?_⟩
  rw [← hae]
  rfl

/-- Removing a reduced regular principal divisor preserves preconnectedness of a spectrum. -/
theorem preconnectedSpace_away_of_radical
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    (t : A) [IsLocalization.Away t S] (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical) [PreconnectedSpace (PrimeSpectrum A)] :
    PreconnectedSpace (PrimeSpectrum S) := by
  refine preconnectedSpace_iff_clopen.mpr fun s hs => ?_
  obtain ⟨z, hz, hzs⟩ := exists_clopen_of_away_radical t ht hrad hs
  rcases (preconnectedSpace_iff_clopen.mp inferInstance) z hz with h | h
  · left
    simpa [h] using hzs.symm
  · right
    simpa [h] using hzs.symm

end Langlands.AlgebraicGeometry
