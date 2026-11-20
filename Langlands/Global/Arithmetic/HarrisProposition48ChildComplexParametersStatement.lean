import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceStatement
import Langlands.Automorphic.Unramified.IsobaricHeckeComplexPlaceParameterStatement

/-! # The induced infinity type of an actual one-place child -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.LocalFactor.Archimedean

/-- The totally complex form of the Hecke-family endpoint comparison, using
Euler constituent recovery only over the actual totally complex top field. -/
def IsobaricHeckeComplexPlaceParameterTCStatement : Prop :=
  CuspidalEulerConstituentRecoveryTCStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
      [CompactSpace (AdeleQuotient F)] (n : ℕ) (A : IsobaricData F)
      (χ : Fin n → HeckeCharacter F),
      A.HasHeckeFamily.{uF, uV} χ →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (ds : List ComplexCharacterData),
          A.HasComplexPlaceParameter v ds ↔ HeckeCharacter.FamilyHasComplexPlaceParameter χ v ds

end Langlands.Automorphic.Unramified

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- Recover the induced complex-place parameters of a supplied weak monomial
induction in the one-place induction. The child may have the parent's parity.
The comparison uses successive unitary isobaric base changes and their
complex-place compatibility over totally complex fields. -/
def Proposition48AuxiliaryChildComplexParametersStatement : Prop :=
  CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} →
  CyclicWeakBaseChangeComplexPlaceTCStatement.{0, 0, uV, uV} →
  IsobaricHeckeComplexPlaceParameterTCStatement.{0, uV} →
  CuspidalEulerConstituentRecoveryTCStatement.{0, uV} →
    ∀ (R : Proposition48Problem.{uF}) (b : ℕ), R.IsAuxiliaryValidAtParity b →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization R.E r),
      HasUnitaryCentralCharacter S →
      S.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} R.ξ →
      R.HasInducedComplexPlaceParameters S.isoClass

end Langlands.Global.Harris
