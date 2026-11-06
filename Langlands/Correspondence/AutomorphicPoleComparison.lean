import Langlands.Correspondence.PairLCompatibilityComparison
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Twist.AdmissibilityProof

/-!
# Applying the pole criterion to automorphic classes

Supporting helpers for assembly characterization. The representation-side pole
criterion remains an explicit input; this module only transports its tests and
conclusion to the existing automorphic class space.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uA uV

open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance poleComparisonFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance poleComparisonGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance poleComparisonGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Every irreducible admissible smooth representation has an equivalent
automorphic object in the prescribed carrier universe. -/
theorem exists_automorphicObject_equiv {n : ℕ+}
    (J : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n : ℕ) F.Carrier))
    (hJ : J.IsIrreducible) (hJa : J.IsAdmissible) :
    ∃ A : AutomorphicObject.{uF, uA} F n,
      Nonempty (J.representation.Equiv A.obj.representation) := by
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uV, uA}
      p F F.canonicalTopologicalData n J hJ
  exact ⟨⟨K, hK, isAdmissible_of_equiv e hJa⟩, ⟨e⟩⟩

/-- Essential square-integrability implies admissibility after undoing its
open-kernel real-power twist. -/
theorem isAdmissible_of_essentiallySquareIntegrable {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hρ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable ρ) :
    IsAdmissible ρ := by
  obtain ⟨s, hs⟩ := hρ
  exact (isAdmissible_twist_iff
    (realPowerCharacter (F.canonicalTopologicalData.determinantNorm n) (-s)) ρ
    (isOpen_ker_realPowerCharacter _
      (F.canonicalTopologicalData.isOpen_ker_determinantNorm n) (-s))).mp
        hs.isAdmissible

/-- The two objects have certified pair L-polynomials of the same pole order
against every essentially square-integrable object of smaller positive rank. -/
def HaveSameLowerRankPoleOrders
    (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (A B : AutomorphicObject.{uF, uA} F (n + 1).succPNat) : Prop :=
  ∀ r : ℕ, r ≤ n →
      ∀ R : AutomorphicObject.{uF, uA} F r.succPNat,
        F.canonicalTopologicalData.IsEssentiallySquareIntegrable R.obj.representation →
        ∃ P Q : ℂ[X],
          IsAutomorphicPairLPolynomial F ψ ν.val
            (automorphicClassOf F A) (automorphicClassOf F R) P ∧
          IsAutomorphicPairLPolynomial F ψ ν.val
            (automorphicClassOf F B) (automorphicClassOf F R) Q ∧
          RankinSelberg.lPolynomialPoleOrderAtZero P =
            RankinSelberg.lPolynomialPoleOrderAtZero Q

/-- The representation-side criterion yields equality in the original
automorphic class universe from pole-order tests against all essentially
square-integrable automorphic objects in that universe. -/
theorem automorphicClass_eq_of_pole_order_tests
    (hcriterion :
      RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement.{uF, uA, uA})
    (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (A B : AutomorphicObject.{uF, uA} F (n + 1).succPNat)
    (hA : ¬ GeneralLinear.IsSupercuspidal A.obj.representation)
    (htests : HaveSameLowerRankPoleOrders ψ ν n A B) :
    automorphicClassOf F A = automorphicClassOf F B := by
  obtain ⟨J, hJ, ⟨eJ⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uA, max uF uA}
      p F F.canonicalTopologicalData (n + 2) A.obj A.property.1
  obtain ⟨K, hK, ⟨eK⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uA, max uF uA}
      p F F.canonicalTopologicalData (n + 2) B.obj B.property.1
  have hJa : J.IsAdmissible := isAdmissible_of_equiv eJ A.property.2
  have hKa : K.IsAdmissible := isAdmissible_of_equiv eK B.property.2
  have hJn : ¬ GeneralLinear.IsSupercuspidal J.representation :=
    fun h => hA ((GeneralLinear.isSupercuspidal_iff_of_equiv eJ).mpr h)
  have hJK : Nonempty (J.representation.Equiv K.representation) := by
    apply hcriterion p F ψ ν n J K hJ hJa hK hKa hJn
    intro r hr ρ hρ hρs
    obtain ⟨R, ⟨eR⟩⟩ :=
      exists_automorphicObject_equiv.{uF, uA, max uF uA}
        (F := F) (n := r.succPNat) ρ hρ
        (isAdmissible_of_essentiallySquareIntegrable hρs)
    have hRs : F.canonicalTopologicalData.IsEssentiallySquareIntegrable
        R.obj.representation :=
      (F.canonicalTopologicalData.isEssentiallySquareIntegrable_iff_of_equiv eR).mp hρs
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := htests r hr R hRs
    exact ⟨P, Q,
      (isAutomorphicPairLPolynomial_iff F A R J ρ eJ.symm eR).mp hP,
      (isAutomorphicPairLPolynomial_iff F B R K ρ eK.symm eR).mp hQ, hPQ⟩
  obtain ⟨e⟩ := hJK
  exact (automorphicClassOf_eq_iff F A B).mpr ⟨(eJ.trans e).trans eK.symm⟩

end Langlands.Correspondence
