import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.TemperedLFactorProof

/-!
# Certified L-polynomials of analytically tempered actions

Present the original actions by square-integrable normalized block inductions,
apply the published Whittaker-type and tempered L-factor constructions, and
transport their certificates back through actual representation equivalences.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)

/-- Full Whittaker type on the original irreducible analytically tempered
action, with no prescribed relation between its carrier and field universes. -/
theorem analyticTemperedWhittakerType {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π) :
    letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r) π := by
  let := F.canonicalTopologicalData.topology
  let A : SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    SmoothRep.of π htπ.isAdmissible.1
  obtain ⟨k, m, hm, σ, hσ, ⟨e⟩⟩ :=
    temperedSquareIntegrableBlockDecomposition F
      (Classification.temperedBlockExhaustion.{uF,uV} F F.canonicalTopologicalData)
      r A hiπ htπ
  have htype (i : Fin k) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i).representation :=
    squareIntegrableWhittakerType_of_genericity.{uF,max uF uV}
      F (Classification.squareIntegrableGenericity.{uF,max uF uV}
        F F.canonicalTopologicalData) ψ (m i) (σ i).representation
      (hσ i).1 (hσ i).2.1
  exact (normalizedProductWhittakerType.{uF,max uF uV} p F ψ
    r k m hm (fun i => (σ i).representation) htype).of_equiv e.symm

variable (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

/-- A polynomial for the original two actions, its full symmetric certificate,
its open-unit-disk nonvanishing, and full Whittaker type of each action. -/
structure AnalyticTemperedLPolynomialData where
  polynomial : ℂ[X]
  left_type : letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r) π
  right_type : letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType t (standardCharacter ψ t) σ
  spec : IsPadicSymmetricLPolynomial F ψ ν.val π σ polynomial
  poleFree : ∀ z : ℂ, ‖z‖ < 1 → polynomial.eval z ≠ 0

/-- Construct certified L-polynomial data for arbitrary original irreducible
analytically tempered actions in independent carrier universes. -/
def analyticTemperedLPolynomialData
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π)
    (hiσ : Representation.IsIrreducible σ)
    (htσ : F.canonicalTopologicalData.IsTempered σ) :
    AnalyticTemperedLPolynomialData F ψ ν π σ :=
  Classical.choice <| by
    let := F.canonicalTopologicalData.topology
    let A : SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) :=
      SmoothRep.of π htπ.isAdmissible.1
    let B : SmoothRep.{0,uF,uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) :=
      SmoothRep.of σ htσ.isAdmissible.1
    obtain ⟨k, m, hm, α, hα, ⟨e⟩⟩ :=
      temperedSquareIntegrableBlockDecomposition F
        (Classification.temperedBlockExhaustion.{uF,uV} F F.canonicalTopologicalData)
        r A hiπ htπ
    obtain ⟨l, n, hn, β, hβ, ⟨f⟩⟩ :=
      temperedSquareIntegrableBlockDecomposition F
        (Classification.temperedBlockExhaustion.{uF,uW} F F.canonicalTopologicalData)
        t B hiσ htσ
    obtain ⟨P, _Q, hP, _hQ, _hprod, hpole⟩ :=
      temperedLFactor.{uF,max uF uV,max uF uW} p F ψ ν
        r t k l m n hm hn (fun i => (α i).representation)
        (fun j => (β j).representation)
        (fun i => (hα i).1) (fun i => (hα i).2.1)
        (fun j => (hβ j).1) (fun j => (hβ j).2.1)
    exact ⟨{
      polynomial := P
      left_type := analyticTemperedWhittakerType F ψ π hiπ htπ
      right_type := analyticTemperedWhittakerType F ψ σ hiσ htσ
      spec := (IsPadicSymmetricLPolynomial.congr_equiv e.symm f.symm).mp hP
      poleFree := hpole }⟩

end Langlands.RankinSelberg
