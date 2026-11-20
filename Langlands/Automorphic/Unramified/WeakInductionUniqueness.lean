import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Uniqueness of cuspidal weak induction from Euler rigidity -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified
open CuspidalOperatorRealization

/-- For a fixed upstairs cuspidal class, any two supplied downstairs cuspidal
weak inductions of the same rank are equal. -/
def WeakInductionUniquenessStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r m : ℕ) (c d : IsoClass F r) (t : IsoClass E m),
    c.IsWeakInductionOf.{uF, uE, uV, uW} t →
    d.IsWeakInductionOf.{uF, uE, uV, uW} t → c = d

/-- Two weak inductions of one class have attached spectra with equal Euler
denominators at a cofinite set of places. -/
theorem exists_sameEulerPolynomials_of_isWeakInductionOf
    {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    {r m : ℕ} {c d : IsoClass F r} {t : IsoClass E m}
    (hc : c.IsWeakInductionOf.{uF, uE, uV, uW} t)
    (hd : d.IsWeakInductionOf.{uF, uE, uV, uW} t) :
    ∃ s s' : SpectralSystem (FinitePlace F) (r + 1),
      c.HasSpectralSystem.{uF, uV} s ∧ d.HasSpectralSystem.{uF, uV} s' ∧
        s.SameEulerPolynomials s' := by
  obtain ⟨s, e, hs, he, hind⟩ := hc
  obtain ⟨s', e', hs', he', hind'⟩ := hd
  obtain ⟨T, P, hT, rfl⟩ := he
  rw [← hT] at he'
  obtain ⟨Q, rfl⟩ := (IsoClass.hasSpectralSystem_iff T e').mp he'
  have hcommon := hind'.of_sameEulerPolynomials
    (SpectralSystem.sameEulerPolynomials_refl s') (Q.spectralSystem_sameEulerPolynomials P)
  refine ⟨s, s', hs, hs', ?_⟩
  filter_upwards [hind.2, hcommon.2] with v hv hv'
  obtain ⟨_, _, _, hp⟩ := hv
  obtain ⟨_, _, _, hp'⟩ := hv'
  intro _ _
  exact hp.trans hp'.symm

/-- The Euler form of cuspidal constituent recovery gives weak-induction
uniqueness by applying it to two singleton families. -/
theorem weakInductionUniqueness_of_cuspidalEulerConstituentRecovery
    (hRig : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    WeakInductionUniquenessStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r m c d t hc hd
  obtain ⟨s, s', hs, hs', heul⟩ := exists_sameEulerPolynomials_of_isWeakInductionOf hc hd
  let c₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank c
  let d₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank d
  let sc : ∀ i, SpectralSystem (FinitePlace F) (c₁ i).rank := fun _ => s
  let sd : ∀ i, SpectralSystem (FinitePlace F) (d₁ i).rank := fun _ => s'
  have hsum := (IsobaricData.sameEulerPolynomials_finiteSum_one sc).symm.trans
    (heul.trans (IsobaricData.sameEulerPolynomials_finiteSum_one sd))
  obtain ⟨e, he⟩ := hRig F 1 1 c₁ d₁ sc sd (fun _ => hs) (fun _ => hs') hsum
  exact PositiveRankCuspidalClass.ofFixedRank_injective r (he 0)

end Langlands.Automorphic.Unramified
