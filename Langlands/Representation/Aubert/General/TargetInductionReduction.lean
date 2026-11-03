import Langlands.Representation.Aubert.General.TargetInductionComparison
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Preservation and exact-K0 reduction of actual target induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Decomposition

variable {G : Type uG} [Group G] {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- Literal restricted subgroup identities transport the standard semidirect
decomposition to the actual target intersection. -/
theorem geometricTargetDecompositionOfEq (I J K : Finset ι) (n : G)
    (hK : IsSemidirectDecomposition
      ((P K).subgroupOf (M I)) ((M K).subgroupOf (M I)) ((U K).subgroupOf (M I)))
    (hLevi : geometricTargetIntersection (M I) (M J) n = M K)
    (hParabolic : (geometricTargetIntersection (M I) (P J) n).subgroupOf (M I) =
      (P K).subgroupOf (M I))
    (hRadical : (geometricTargetIntersection (M I) (U J) n).subgroupOf (M I) =
      (U K).subgroupOf (M I)) :
    GeometricTargetDecomposition P M U I J n := by
  unfold GeometricTargetDecomposition
  rw [hParabolic, hLevi, hRadical]
  exact hK

end Decomposition

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {M Q L N Q' L' N' : Subgroup G}

private theorem leviNormalizedInductionPreservationOfEq
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M) (hL'M : L' ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (h' : IsSemidirectDecomposition
      (Q'.subgroupOf M) (L'.subgroupOf M) (N'.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hN' : IsClosed (N' : Set G))
    (hLL' : L = L') (hQQ' : Q.subgroupOf M = Q'.subgroupOf M)
    (hNN' : N.subgroupOf M = N'.subgroupOf M)
    (hfl : letI := hM.locallyCompactSpace
      PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h'
        (hN'.preimage continuous_subtype_val)) ∧
      PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} h'
        (hN'.preimage continuous_subtype_val))) :
    PreservesFiniteLength (leviNormalizedInductionFunctor.{uG, uV} hM hLM h hN) ∧
    PreservesFiniteLengthShortExact
      (leviNormalizedInductionFunctor.{uG, uV} hM hLM h hN) := by
  subst L'
  let _ := hM.locallyCompactSpace
  have hl := (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hL'M)).comp
    hfl.1
  have hx := PreservesFiniteLengthShortExact.comp
    (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hL'M))
    (pullbackFunctor_preservesShortExact (subgroupOfContinuousEquiv hL'M)) hfl.2
  let e := (Functor.isoWhiskerRight
    (conjugationFunctorOneNatIso (identityConjugationMembership (rfl : L = L)))
    (leviNormalizedInductionFunctor.{uG, uV} hM hL'M h' hN') ≪≫
      Functor.leftUnitor _).symm ≪≫
    leviNormalizedInductionIsoOfEq hM hLM hL'M h h' hN hN' rfl hQQ' hNN'
  exact ⟨hl.of_iso e, hx.of_iso e⟩

end Levi

section Preservation

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))
  (I J K : Finset ι) (n : G)
  (ht : GeometricTargetDecomposition P M U I J n)
  (hKI : M K ≤ M I)
  (hK : IsSemidirectDecomposition
    ((P K).subgroupOf (M I)) ((M K).subgroupOf (M I)) ((U K).subgroupOf (M I)))
  (hLevi : geometricTargetIntersection (M I) (M J) n = M K)
  (hParabolic : (geometricTargetIntersection (M I) (P J) n).subgroupOf (M I) =
    (P K).subgroupOf (M I))
  (hRadical : (geometricTargetIntersection (M I) (U J) n).subgroupOf (M I) =
    (U K).subgroupOf (M I))
  (hfl : letI := (hM I).locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} hK
      ((hU K).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} hK
      ((hU K).preimage continuous_subtype_val)))

include hKI hK hLevi hParabolic hRadical hfl in
/-- Preservation of the literal standard induction supplies finite-length and
short-exact preservation for the actual target-intersection induction. -/
theorem geometricTargetInductionPreservationOfEq :
    PreservesFiniteLength (geometricTargetInductionFunctor.{uI, uG, uV}
      P M U hM hU I J n ht) ∧
    PreservesFiniteLengthShortExact (geometricTargetInductionFunctor.{uI, uG, uV}
      P M U hM hU I J n ht) :=
  leviNormalizedInductionPreservationOfEq (hM I) inf_le_left hKI ht hK
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)
    (hU K) hLevi hParabolic hRadical hfl

/-- The actual target induction on exact finite-length K0, with preservation
derived from the displayed standard induction. -/
def geometricTargetInductionK0 :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ
        (geometricTargetIntersection (M I) (M J) n) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M I) :=
  FiniteLengthGrothendieckGroup.map
    (geometricTargetInductionFunctor.{uI, uG, uV} P M U hM hU I J n ht)
    (geometricTargetInductionPreservationOfEq
      P M U hM hU I J K n ht hKI hK hLevi hParabolic hRadical hfl).1
    (geometricTargetInductionPreservationOfEq
      P M U hM hU I J K n ht hKI hK hLevi hParabolic hRadical hfl).2

/-- The actual target map equals the literal restricted induction, preceded
by the identity identification of equal ambient fine Levis and its canonical
subgroupOf transport. -/
theorem geometricTargetInductionK0OfEq :
    let _ := (hM I).locallyCompactSpace
    geometricTargetInductionK0.{uI, uG, uV}
        P M U hM hU I J K n ht hKI hK hLevi hParabolic hRadical hfl =
      ((FiniteLengthGrothendieckGroup.map
        (normalizedInductionFunctor hK ((hU K).preimage continuous_subtype_val))
          hfl.1 hfl.2).comp
        (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hKI))).comp
        (conjugationK0.{uG, uV} 1 (identityConjugationMembership hLevi)) := by
  let _ := (hM I).locallyCompactSpace
  have htfl := geometricTargetInductionPreservationOfEq.{uI, uG, uV}
    P M U hM hU I J K n ht hKI hK hLevi hParabolic hRadical hfl
  have hl := (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hKI)).comp
    hfl.1
  have hx := PreservesFiniteLengthShortExact.comp
    (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hKI))
    (pullbackFunctor_preservesShortExact (subgroupOfContinuousEquiv hKI)) hfl.2
  have hcl := (pullbackFunctor_preservesFiniteLength
    (conjugationEquiv 1 (identityConjugationMembership hLevi))).comp hl
  have hcx := PreservesFiniteLengthShortExact.comp
    (pullbackFunctor_preservesFiniteLength
      (conjugationEquiv 1 (identityConjugationMembership hLevi)))
    (pullbackFunctor_preservesShortExact
      (conjugationEquiv 1 (identityConjugationMembership hLevi))) hx
  have heq := FiniteLengthGrothendieckGroup.map_eq_of_iso
    (geometricTargetInductionComparisonIso.{uI, uG, uV}
      P M U hM hU I J K n ht hKI hK hLevi hParabolic hRadical)
    hcl hcx htfl.1 htfl.2
  unfold conjugationFunctor leviNormalizedInductionFunctor at heq
  rw [FiniteLengthGrothendieckGroup.map_comp _ _
      (pullbackFunctor_preservesFiniteLength _) (pullbackFunctor_preservesShortExact _)
      hl hx hcl hcx,
    FiniteLengthGrothendieckGroup.map_comp _ _
      (pullbackFunctor_preservesFiniteLength _) (pullbackFunctor_preservesShortExact _)
      hfl.1 hfl.2 hl hx] at heq
  exact heq.symm

end Preservation

end Langlands.Aubert.General
