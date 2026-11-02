import Langlands.Global.Factors.PolePairingDescentStatement
import Langlands.Global.Factors.MeromorphicPoleComparisonProof
import Langlands.VirtualRepresentation.DescentProof

/-!
# Pole orders, generator pairings and generated integral isometry
-/

noncomputable section

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation

universe u v w x y

theorem poleGramComparison (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : PoleGramComparisonStatement ι κ J A B := by
  intro left right d hregular hleft hright j k
  obtain ⟨hlm, hrm, hlu, hru, hlb, hrb, heq⟩ := hregular j k
  have horder := completedPoleTransfer A B
    (d.leftPlaces j k) (d.rightPlaces j k) (d.left j k) (d.right j k)
    (d.leftOmitted j k) (d.rightOmitted j k)
    (d.leftBoundary j k) (d.rightBoundary j k) 0 hlm hrm hlu hru hlb hrb heq
  rw [hleft j k, hright j k] at horder
  exact neg_injective (WithTop.coe_inj.mp horder)

theorem generatedPositiveIsometry_of_gram {ι : Type u} {κ : Type v} {J : Type w}
    (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (sourceWeight : ι → ℕ) (targetWeight : κ → ℕ)
    (hpair : ∀ j k, pairing (left j) (left k) = pairing (right j) (right k))
    (hdegree : ∀ j, degree targetWeight (right j) = degree sourceWeight (left j)) :
    relations left = relations right ∧
    ∃! T : generated left ≃ₗ[ℤ] generated right,
      GeneratedPositiveIsometry left right sourceWeight targetWeight T := by
  have hrelations := integralRelationDescent ι κ J left right hpair
  obtain ⟨T, hT, hunique⟩ := integralGeneratedEquivalence ι κ J left right hrelations
  have hisometry := integralGeneratedIsometry ι κ J left right hpair T.toLinearMap hT
  have hdegrees := integralGeneratedDegree ι κ J left right sourceWeight targetWeight
    hdegree T.toLinearMap hT
  refine ⟨hrelations, T, ⟨hT, hisometry, hdegrees, ?_⟩, ?_⟩
  · intro a hnorm hpositive
    apply integralPositiveDegreeBasis κ targetWeight (T a)
    · exact (hisometry a a).trans hnorm
    · exact lt_of_lt_of_eq hpositive (hdegrees a).symm
  · intro S hS
    exact hunique S hS.1

theorem poleGeneratedDescent (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : PoleGeneratedDescentStatement ι κ J A B := by
  intro left right sourceWeight targetWeight rank d hleftDegree hrightDegree
    hregular hleft hright
  apply generatedPositiveIsometry_of_gram left right sourceWeight targetWeight
  · exact poleGramComparison ι κ J A B left right d hregular hleft hright
  · intro j
    exact (hrightDegree j).trans (hleftDegree j).symm

theorem polePairingDescent (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : PolePairingDescentStatement ι κ J A B :=
  ⟨poleGramComparison ι κ J A B, poleGeneratedDescent ι κ J A B⟩

end Langlands.Global.PoleComparison
