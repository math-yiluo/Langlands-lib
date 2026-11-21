import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness

open scoped NumberField

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open IsDedekindDomain.HeightOneSpectrum

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

namespace IsobaricData

private theorem eq_of_attached_sameEulerPolynomials [NumberField.IsTotallyComplex F]
    (hRigid : Unramified.CuspidalEulerConstituentRecoveryTCStatement.{uF, uV})
    {D D' : IsobaricData F} {s : SpectralSystem (FinitePlace F) D.rank}
    {t : SpectralSystem (FinitePlace F) D'.rank}
    (hs : HasSpectralSystem.{uF, uV} D s) (ht : HasSpectralSystem.{uF, uV} D' t)
    (hst : s.SameEulerPolynomials t) : D = D' := by
  obtain ⟨p, c, hc, a, ha, has⟩ := hs
  obtain ⟨q, d, hd, b, hb, hbt⟩ := ht
  obtain ⟨e, he⟩ := hRigid F p q c d a b ha hb (has.trans (hst.trans hbt.symm))
  rw [← hc, ← hd]
  simp only [show c = d ∘ e from funext he, ← Multiset.map_map, Multiset.map_univ_val_equiv]

variable {E : Type uE} [Field E] [NumberField E] [Algebra F E]
  [CompactSpace (AdeleQuotient E)]

omit [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] in
private theorem arithmeticWeakBaseChange_sameEulerPolynomials {n : ℕ}
    {s : SpectralSystem (FinitePlace F) n} {t t' : SpectralSystem (FinitePlace E) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) (h' : t'.IsArithmeticWeakBaseChangeOf s) :
    t.SameEulerPolynomials t' := by
  filter_upwards [tendsto_under_cofinite.eventually h, tendsto_under_cofinite.eventually h']
    with w hw hw'
  intro ht ht'
  let q : FinitePlacesAbove E (w.under (𝓞 F)) := ⟨w, liesOver_under w⟩
  obtain ⟨_, _, _, he⟩ := hw
  obtain ⟨_, _, _, he'⟩ := hw'
  exact congrArg Eigenvalues.eulerPolynomial ((he q).trans (he' q).symm)

private theorem sameEulerPolynomials_cast {I : Type*} {n m : ℕ}
    (h : n = m) (s : SpectralSystem I n) :
    s.SameEulerPolynomials (h ▸ s : SpectralSystem I m) := by
  subst m
  exact SpectralSystem.sameEulerPolynomials_refl s

/-- Euler constituent recovery over `E` makes weak base change of isobaric data unique,
including the multiplicities of the cuspidal constituents. -/
theorem IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC
    [NumberField.IsTotallyComplex E]
    (hRigid : Unramified.CuspidalEulerConstituentRecoveryTCStatement.{uE, uW})
    {DF : IsobaricData F} {DE DE' : IsobaricData E}
    (h : IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF)
    (h' : IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF) : DE = DE' := by
  obtain ⟨hn, s, t, hs, ht, hst⟩ := h
  obtain ⟨hm, s', t', hs', ht', hst'⟩ := h'
  have hss' := hs'.sameEulerPolynomials hs
  have hst'' := hst'.of_sameEulerPolynomials hss' (SpectralSystem.sameEulerPolynomials_refl _)
  have he := arithmeticWeakBaseChange_sameEulerPolynomials hst hst''
  exact eq_of_attached_sameEulerPolynomials hRigid ht ht'
    ((sameEulerPolynomials_cast hn t).trans (he.trans (sameEulerPolynomials_cast hm t').symm))

end IsobaricData

namespace Unramified

/-- Totally complex Euler constituent recovery gives uniqueness of actual isobaric
weak base change for number-field extensions with totally complex upper field. -/
def IsobaricWeakBaseChangeUniquenessTCStatement : Prop :=
  CuspidalEulerConstituentRecoveryTCStatement.{uE, uW} →
    ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
      [NumberField.IsTotallyComplex E] [Algebra F E] [CompactSpace (AdeleQuotient F)]
      [CompactSpace (AdeleQuotient E)] (DF : IsobaricData F) (DE DE' : IsobaricData E),
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF →
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF → DE = DE'

theorem isobaricWeakBaseChangeUniquenessTC :
    IsobaricWeakBaseChangeUniquenessTCStatement.{uF, uE, uV, uW} := by
  intro hRecovery F E _ _ _ _ _ _ _ _ DF DE DE' h h'
  exact IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC hRecovery h h'

end Unramified

end Langlands.Automorphic
