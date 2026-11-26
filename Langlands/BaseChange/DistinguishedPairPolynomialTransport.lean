import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Global.Factors.DistinguishedFiniteStandardEpsilon
import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldLPolynomial
import Langlands.Representation.RankinSelberg.StableTwist.GammaCharacterChange

/-! # Transport of actual pair denominators from a distinguished completion -/

noncomputable section

set_option autoImplicit false

universe uF uD uV uW

namespace Langlands.BaseChange

open Correspondence GeneralLinear HarmonicAnalysis MeasureTheory RankinSelberg Whittaker
open Global.CuspidalPairFunctionalEquation
open LocalFactor.PadicAbelian (SelfDualHaar)

/-- A pair of given local actions and a pair of generic classes over a
bicontinuously isomorphic field have the same certified denominators whenever
the actual class representatives pull back to the given actions. -/
def DistinguishedPairPolynomialTransportStatement : Prop :=
  ∀ (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (F : PadicField.{uF} p) (D : PadicField.{uD} q),
    letI := F.canonicalTopologicalData.topology
    letI := D.canonicalTopologicalData.topology
    ∀ (a : F.Carrier ≃+* D.Carrier), Continuous a → Continuous a.symm →
    ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
      (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
      (A B : AutomorphicObject.{uD,uD} D r.succPNat),
      Nonempty (ρ.Equiv (A.obj.representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) →
      Nonempty (τ.Equiv (B.obj.representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) →
    ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (νF : SelfDualHaar F.canonicalTopologicalData ψF)
      (ψD : NontrivialAdditiveCharacter D) (νD : SelfDualHaar D.canonicalTopologicalData ψD),
      IsGeneric ψD r A.obj.representation → IsGeneric ψD r B.obj.representation →
    ∀ (P Q : Polynomial ℂ),
      IsPadicRankLPolynomial F ψF νF.val ρ τ P →
      IsAutomorphicPairLPolynomial D ψD νD.val (automorphicClassOf D A) (automorphicClassOf D B) Q →
      P = Q

/-- Remove the class packaging on the generic pair, pull the JPSS polynomial
back along the field isomorphism, and use character and measure invariance. -/
theorem distinguishedPairPolynomialTransport :
    DistinguishedPairPolynomialTransportStatement.{uF,uD,uV,uW} := by
  intro p q _ _ F D
  let TF := F.canonicalTopologicalData
  let TD := D.canonicalTopologicalData
  let := TF.topology
  let := TD.topology
  intro a ha ha' r V _ _ W _ _ ρ τ A B ⟨eρ⟩ ⟨eτ⟩ ψF νF ψD νD hA hB P Q hP hQ
  let := TF.valuativeRel
  let := TD.valuativeRel
  let := TF.localField
  let := TD.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel D.Carrier
  let : BorelSpace D.Carrier := ⟨rfl⟩
  let ψ := completionAdditivePullback D a ha ψD
  let ν := completionHaarPullback D a ha ha' νD.val
  have hψ (x : F.Carrier) : ψD (a x) = ψ x := rfl
  have hν : νD.val.measure = ν.measure.map a :=
    (congrArg AdditiveHaarMeasure.measure
      (HarmonicAnalysis.FieldTransport.haarMeasure_symm a.symm ha' ha νD.val)).symm
  have hQD := (isAutomorphicPairLPolynomial_iff D A B A.obj B.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hQ
  have hcert := (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp
    (hQD.isPadicSymmetricLPolynomial (ν := νD) hA hB)
  have hpull : IsPadicPairLPolynomial F ψ ν
      (A.obj.representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom))
      (B.obj.representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom)) Q :=
    (RankinSelberg.FieldTransport.isLocalPairLPolynomial_comp_iff a ha ha' hψ hν
      A.obj.representation B.obj.representation Q).mp hcert
  have hQF := (IsPadicPairLPolynomial.congr_equiv eρ.symm eτ.symm).mp hpull
  obtain ⟨c, hc⟩ := TF.exists_unit_scale_eq ψF ψ
  have hPF := (RankinSelberg.Padic.isPadicPairLPolynomial_characterChange F ψF c νF.val ρ τ P).mp
    ((isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp (isPadicRankLPolynomial_succ.mp hP))
  rw [hc] at hPF
  exact hPF.unique_of_measure hQF

end Langlands.BaseChange
