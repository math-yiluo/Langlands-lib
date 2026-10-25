import Langlands.Automorphic.CuspidalSpectralPresentation

/-! # Jacquet--Shalika rigidity for supplied cuspidal spectral systems

These proposition targets use actual full cuspidal classes, with mixed positive
ranks and genuine spectral attachments. They assert neither the existence of
attachments for arbitrary classes nor the realization of an isobaric sum.
-/

noncomputable section

open scoped BigOperators

universe uF uV

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified

/-- JS81 Theorem 4.2: distinct full cuspidal classes of mixed positive ranks
have independent traces at all positive powers outside one finite set. -/
def CuspidalPowerTraceIndependenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (p : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    Function.Injective c →
    ∀ (S : Finset (FinitePlace F)) (hS : ∀ i, (s i).exceptional ⊆ S)
      (a : Fin p → ℂ),
      (∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
        (∑ i, a i * (s i).powerTrace v (fun h => hv (hS i h)) k) = 0) →
      ∀ i, a i = 0

/-- The numerical constituent-recovery step in JS81 Theorem 4.4: equality of
all positive trace sums recovers the full cuspidal list with multiplicity. -/
def CuspidalPowerTraceConstituentRecoveryStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SamePowerTraces (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

/-- Euler-polynomial form of the same numerical recovery step. Each side is
the product of the supplied normalized local Euler denominator polynomials. -/
def CuspidalEulerConstituentRecoveryStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

/-- The coherent mixed-rank cuspidal spectral rigidity targets. -/
def CuspidalSpectralRigidityStatement : Prop :=
  CuspidalPowerTraceIndependenceStatement.{uF, uV} ∧
  CuspidalPowerTraceConstituentRecoveryStatement.{uF, uV} ∧
  CuspidalEulerConstituentRecoveryStatement.{uF, uV}

end Langlands.Automorphic.Unramified
