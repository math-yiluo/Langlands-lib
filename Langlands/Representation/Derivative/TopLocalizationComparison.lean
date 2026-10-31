import Langlands.Representation.Derivative.TopLocalizationBoundary
import Langlands.Representation.Derivative.TopLocalizationRestriction
import Langlands.Representation.Derivative.TopLocalizationStep
import Langlands.Representation.Derivative.TopLocalizationMirabolicZero
import Mathlib.CategoryTheory.Whiskering

/-! # The all-rank full upper localization comparison -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.TopLocalization

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Iterating the actual normalized `Φ⁻` steps leaves precisely the terminal
full upper quotient. -/
def mirabolicIteratedIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    mirabolicUpperCoinvariantsFunctor.{uF,uV} ψ.complex (0 + n) ≅
      phiMinusIterate T ψ 0 n ⋙ mirabolicUpperCoinvariantsFunctor ψ.complex 0 := by
  letI := T.topology
  induction n with
  | zero => exact (Functor.leftUnitor _).symm
  | succ n ih =>
      exact (stepIso T ψ (0 + n)).symm ≪≫
        Functor.isoWhiskerLeft (Mirabolic.phiMinus T ψ (0 + n)) ih ≪≫
        (Functor.associator _ _ _).symm

/-- The full upper quotient is the actual normalized mirabolic top derivative. -/
def mirabolicLocalizationIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    mirabolicUpperCoinvariantsFunctor.{uF,uV} ψ.complex (0 + n) ≅
      mirabolicDerivative T ψ 0 n := by
  letI := T.topology
  exact mirabolicIteratedIso T ψ n ≪≫
    Functor.isoWhiskerLeft (phiMinusIterate T ψ 0 n) (mirabolicZeroIso T ψ.complex)

/-- Restriction followed by the normalized minus tower computes the full
upper quotient at every positive source rank. -/
def positiveLocalizationIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ.complex (0 + n + 1) ≅
      generalLinearDerivativePositive T ψ 0 n := by
  letI := T.topology
  exact upperRestrictionIso T ψ.complex (0 + n) ≪≫
    Functor.isoWhiskerLeft (generalLinearRestriction T (0 + n))
      (mirabolicLocalizationIso T ψ n)

/-- Rank transport preserves the full upper quotient naturally. -/
def upperRankCastIso (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ a ≅
      generalLinearRankCast T h ⋙ PartialTensor.upperCoinvariantsFunctor ψ b := by
  letI := T.topology
  subst b
  exact (Functor.leftUnitor _).symm

/-- The exact positive-rank equation for the published top derivative. -/
theorem topDerivative_succ (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    topDerivative.{uF,uV} T ψ (n + 1) =
      generalLinearRankCast T (Nat.zero_add (n + 1)).symm ⋙
        generalLinearDerivativePositive T ψ 0 n := by
  let := T.topology
  exact (topDerivative_eq T ψ (n + 1)).trans
    (generalLinearDerivative_top_succ T ψ n (Nat.le_refl _))

/-- In every rank, the full upper quotient is naturally the published
normalized top derivative on its entire `GL₀` representation carrier. -/
def topLocalizationIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    (m : ℕ) → letI := T.topology
      PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ.complex m ≅
        topDerivative T ψ m
  | 0 => topLocalizationZeroIso T ψ
  | n + 1 => by
      letI := T.topology
      exact upperRankCastIso T ψ.complex (Nat.zero_add (n + 1)).symm ≪≫
        Functor.isoWhiskerLeft
          (generalLinearRankCast T (Nat.zero_add (n + 1)).symm)
          (positiveLocalizationIso T ψ n) ≪≫
        (eqToIso (topDerivative_succ T ψ n)).symm

end Langlands.Derivative.TopLocalization
