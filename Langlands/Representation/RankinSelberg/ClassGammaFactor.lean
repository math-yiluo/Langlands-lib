import Langlands.Representation.RankinSelberg.PadicGammaFactor

/-!
# Gamma construction on supercuspidal isomorphism classes

Apply the canonical p-adic construction to representatives with explicit
analytic input, then descend its result through the published class relation.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r n : ℕ}
  (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
  (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))

/-- Some representatives of the two classes satisfy the explicit canonical
p-adic gamma inputs. This includes `n ≤ r`; it is a sufficient input
proposition, not an assertion of analytic existence. -/
def ClassGammaInput : Prop :=
  letI := F.canonicalTopologicalData.topology
  ∃ (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
    (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)),
    Quotient.mk _ A = π ∧ Quotient.mk _ B = τ ∧
      PadicPairGammaInput F ψ ν A.obj.representation B.obj.representation

/-- Construct the actual rational gamma unit on supercuspidal classes using the
existing `IsClassGammaFactor`, rather than a new class relation. -/
def classGammaFactor (h : ClassGammaInput F ψ ν π τ) :
    {G : RationalFunctionsˣ // IsClassGammaFactor F ψ ν π τ (G : RationalFunctions)} := by
  letI := F.canonicalTopologicalData.topology
  let A := Classical.choose h
  let B := Classical.choose (Classical.choose_spec h)
  have hab := Classical.choose_spec (Classical.choose_spec h)
  let G := padicPairGammaFactor F ψ ν A.obj.representation B.obj.representation hab.2.2
  refine ⟨G.val, ?_⟩
  exact Eq.mp (congrArg₂
    (fun a b => IsClassGammaFactor F ψ ν a b (G.val : RationalFunctions)) hab.1 hab.2.1)
    ((isClassGammaFactor_mk F ψ ν A B _).mpr G.property)

variable {F ψ ν π τ}

/-- Any two supplied analytic witnesses yield the same unit, by the published
class-level uniqueness theorem. -/
theorem classGammaFactor_independent
    (h h' : ClassGammaInput F ψ ν π τ) :
    (classGammaFactor F ψ ν π τ h).val = (classGammaFactor F ψ ν π τ h').val := by
  apply Units.ext
  exact (classGammaFactor F ψ ν π τ h).property.unique
    (classGammaFactor F ψ ν π τ h').property

/-- The constructed value agrees with any gamma factor satisfying the class
relation, including a value obtained from other representatives. -/
theorem classGammaFactor_eq {G : RationalFunctions}
    (h : ClassGammaInput F ψ ν π τ) (hG : IsClassGammaFactor F ψ ν π τ G) :
    ((classGammaFactor F ψ ν π τ h).val : RationalFunctions) = G :=
  (classGammaFactor F ψ ν π τ h).property.unique hG

end Langlands.RankinSelberg
