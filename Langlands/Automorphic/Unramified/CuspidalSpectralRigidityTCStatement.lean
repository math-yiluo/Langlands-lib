import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally complex forms of Jacquet–Shalika rigidity for supplied cuspidal spectral systems

`CuspidalPowerTraceIndependenceStatement`, `CuspidalPowerTraceConstituentRecoveryStatement`,
`CuspidalEulerConstituentRecoveryStatement` and their conjunction
`CuspidalSpectralRigidityStatement`, each with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the same universe
levels, the rest verbatim. Proposition definitions only. See the paired Markdown for the
reason (the Library's route to the local correspondence applies these statements only over
totally complex fields) and the sources.
-/

noncomputable section

open scoped BigOperators

universe uF uV

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified

/-- The totally complex form of `CuspidalPowerTraceIndependenceStatement` (JS81 Theorem 4.2):
over a totally complex number field, distinct full cuspidal classes of mixed positive ranks
have independent traces at all positive powers outside one finite set. -/
def CuspidalPowerTraceIndependenceTCStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (p : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    Function.Injective c →
    ∀ (S : Finset (FinitePlace F)) (hS : ∀ i, (s i).exceptional ⊆ S)
      (a : Fin p → ℂ),
      (∀ (v : FinitePlace F) (hv : v ∉ S) (k : ℕ), 0 < k →
        (∑ i, a i * (s i).powerTrace v (fun h => hv (hS i h)) k) = 0) →
      ∀ i, a i = 0

/-- The totally complex form of `CuspidalPowerTraceConstituentRecoveryStatement` (the
numerical step of JS81 Theorem 4.4): over a totally complex number field, equality of all
positive trace sums recovers the full cuspidal list with multiplicity. -/
def CuspidalPowerTraceConstituentRecoveryTCStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SamePowerTraces (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

/-- The totally complex form of `CuspidalEulerConstituentRecoveryStatement` (Euler-polynomial
form of the same numerical recovery step), over a totally complex number field. -/
def CuspidalEulerConstituentRecoveryTCStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
    (d : Fin q → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
    (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
    (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) →
    ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i)

/-- The totally complex form of `CuspidalSpectralRigidityStatement` (Harris's input 9 in
`Proposition48ReductionStatement`): the conjunction of the three totally complex forms. -/
def CuspidalSpectralRigidityTCStatement : Prop :=
  CuspidalPowerTraceIndependenceTCStatement.{uF, uV} ∧
  CuspidalPowerTraceConstituentRecoveryTCStatement.{uF, uV} ∧
  CuspidalEulerConstituentRecoveryTCStatement.{uF, uV}

end Langlands.Automorphic.Unramified
