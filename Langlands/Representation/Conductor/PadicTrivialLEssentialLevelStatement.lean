import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalFactor.Abelian.Padic
import Langlands.Representation.Whittaker.DualTransform

/-!
# The p-adic essential-vector level with trivial L-polynomials

A specialization of JPSS 1981, Theorem (5.1)(ii), first clause, using the
unit L-polynomial case discussed in Jacquet 2012, Remark 1.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV

/-- If the p-adic pair L-polynomials of `π` and its inverse-transpose pullback
against the trivial character are both `1`, then every essential vector in a
nonzero Whittaker model of `π` is fixed by `K_(n+2)(m)` when the pair epsilon
factor is `c q^(-ms)`. -/
def PadicTrivialLEssentialVectorLevelStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (n : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ [MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier)]
      [BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier)]
      [MeasurableSpace (upperUnipotent (n + 1) F.Carrier)]
      [BorelSpace (upperUnipotent (n + 1) F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient n F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier)]
      [MeasurableSpace (Langlands.GeneralLinear 1 F.Carrier)]
      [BorelSpace (Langlands.GeneralLinear 1 F.Carrier)]
      (q : ℕ) (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
      (μ : Measure (LeftUnipotentQuotient n F.Carrier))
      (h : IsJacquetNormalization q ψ abv ϖ μ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F.Carrier) V),
      IsGeneric ψ (n + 1) π →
      IsPadicSymmetricLPolynomial F ψ ν.val π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 →
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val (inverseTransposePullback π)
        (inverseTransposePullback (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))) 1 →
      ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∀ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w →
      ∀ (c : ℂˣ) (m : ℕ),
        IsPadicSymmetricEpsilonFactor F ψ ν.val π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
          (c, (m : ℤ)) →
        w ∈ levelFixedVectors (V := (coefficientModel π ℓ).toSubmodule)
          (modelRepresentation π ℓ) m

end Langlands.Conductor
