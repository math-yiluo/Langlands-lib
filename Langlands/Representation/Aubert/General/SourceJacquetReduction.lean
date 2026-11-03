import Langlands.Representation.Aubert.General.SourceJacquetComparison
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Decomposition and exact-K0 reduction of an actual source Jacquet term -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Decomposition

variable {G : Type uG} [Group G] {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- The three exact restricted subgroup identities transport the standard
semidirect decomposition to the actual geometric source. -/
theorem geometricSourceDecompositionOfEq (I J K : Finset ι) (n : G)
    (hK : IsSemidirectDecomposition
      ((P K).subgroupOf (M J)) ((M K).subgroupOf (M J)) ((U K).subgroupOf (M J)))
    (hParabolic : (geometricSourceIntersection (P I) (M J) n).subgroupOf (M J) =
      (P K).subgroupOf (M J))
    (hLevi : geometricSourceIntersection (M I) (M J) n = M K)
    (hRadical : (geometricSourceIntersection (U I) (M J) n).subgroupOf (M J) =
      (U K).subgroupOf (M J)) :
    GeometricSourceDecomposition P M U I J n := by
  unfold GeometricSourceDecomposition
  rw [hParabolic, hLevi, hRadical]
  exact hK

end Decomposition

section Preservation

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))
  (I J K : Finset ι) (n : G)
  (hs : GeometricSourceDecomposition P M U I J n)
  (hKJ : M K ≤ M J)
  (hK : IsSemidirectDecomposition
    ((P K).subgroupOf (M J)) ((M K).subgroupOf (M J)) ((U K).subgroupOf (M J)))
  (hLevi : geometricSourceIntersection (M I) (M J) n = M K)
  (hRadical : (geometricSourceIntersection (U I) (M J) n).subgroupOf (M J) =
    (U K).subgroupOf (M J))
  (hfl : letI := (hM J).locallyCompactSpace
    PreservesFiniteLength (jacquetFunctor.{uG, uV} hK
      ((hU K).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (jacquetFunctor.{uG, uV} hK
      ((hU K).preimage continuous_subtype_val)))

include hKJ hK hLevi hRadical hfl in
/-- Finite-length and short-exact preservation of the literal restricted
Jacquet functor imply both properties for the actual geometric source functor.
The identity change of acting group is reflected, not assumed. -/
theorem geometricSourceJacquetPreservationOfEq :
    PreservesFiniteLength (geometricSourceJacquetFunctor.{uI, uG, uV}
      P M U hM hU I J n hs) ∧
    PreservesFiniteLengthShortExact (geometricSourceJacquetFunctor.{uI, uG, uV}
      P M U hM hU I J n hs) := by
  let _ := (hM J).locallyCompactSpace
  have hl := hfl.1.comp
    (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hKJ).symm)
  have hx := PreservesFiniteLengthShortExact.comp hfl.1 hfl.2
    (pullbackFunctor_preservesShortExact (subgroupOfContinuousEquiv hKJ).symm)
  let e := geometricSourceJacquetComparisonIso.{uI, uG, uV}
    P M U hM hU I J K n hs hKJ hK hLevi hRadical
  have hl' := hl.of_iso e.symm
  have hx' := hx.of_iso e.symm
  constructor
  · intro A hA
    exact (FiniteLengthAssembly.finiteLength_comp_surjective_iff
      ((geometricSourceJacquetFunctor P M U hM hU I J n hs).obj A).representation
      (conjugationEquiv 1 (identityConjugationMembership hLevi)).toMonoidHom
      (conjugationEquiv 1 (identityConjugationMembership hLevi)).surjective).mpr
        (hl' A hA)
  · intro A B C f g hA hB hC h
    exact hx' f g hA hB hC h

/-- The actual source Jacquet map on the exact finite-length Grothendieck
group, using preservation derived from the literal standard restriction. -/
def geometricSourceJacquetK0 :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ
        (geometricSourceIntersection (M I) (M J) n) :=
  FiniteLengthGrothendieckGroup.map
    (geometricSourceJacquetFunctor.{uI, uG, uV} P M U hM hU I J n hs)
    (geometricSourceJacquetPreservationOfEq
      P M U hM hU I J K n hs hKJ hK hLevi hRadical hfl).1
    (geometricSourceJacquetPreservationOfEq
      P M U hM hU I J K n hs hKJ hK hLevi hRadical hfl).2

/-- On the full exact Grothendieck group, the actual source Jacquet map,
followed by identity identification of its Levi, is the literal restricted
standard Jacquet map transported from the subgroupOf Levi. -/
theorem geometricSourceJacquetK0OfEq :
    let _ := (hM J).locallyCompactSpace
    (conjugationK0.{uG, uV} 1 (identityConjugationMembership hLevi)).comp
      (geometricSourceJacquetK0.{uI, uG, uV}
        P M U hM hU I J K n hs hKJ hK hLevi hRadical hfl) =
      (FiniteLengthGrothendieckGroup.pullback
        (subgroupOfContinuousEquiv hKJ).symm).comp
        (FiniteLengthGrothendieckGroup.map
          (jacquetFunctor hK ((hU K).preimage continuous_subtype_val)) hfl.1 hfl.2) := by
  let _ := (hM J).locallyCompactSpace
  have hsfl := geometricSourceJacquetPreservationOfEq.{uI, uG, uV}
    P M U hM hU I J K n hs hKJ hK hLevi hRadical hfl
  have hl := hfl.1.comp
    (pullbackFunctor_preservesFiniteLength (subgroupOfContinuousEquiv hKJ).symm)
  have hx := PreservesFiniteLengthShortExact.comp hfl.1 hfl.2
    (pullbackFunctor_preservesShortExact (subgroupOfContinuousEquiv hKJ).symm)
  have hsl := hsfl.1.comp
    (pullbackFunctor_preservesFiniteLength
      (conjugationEquiv 1 (identityConjugationMembership hLevi)))
  have hsx := PreservesFiniteLengthShortExact.comp hsfl.1 hsfl.2
    (pullbackFunctor_preservesShortExact
      (conjugationEquiv 1 (identityConjugationMembership hLevi)))
  have heq := FiniteLengthGrothendieckGroup.map_eq_of_iso
    (geometricSourceJacquetComparisonIso.{uI, uG, uV}
      P M U hM hU I J K n hs hKJ hK hLevi hRadical)
    hsl hsx hl hx
  unfold conjugationFunctor leviNormalizedJacquetFunctor at heq
  rw [FiniteLengthGrothendieckGroup.map_comp _ _ hsfl.1 hsfl.2
      (pullbackFunctor_preservesFiniteLength _)
      (pullbackFunctor_preservesShortExact _) hsl hsx,
    FiniteLengthGrothendieckGroup.map_comp _ _ hfl.1 hfl.2
      (pullbackFunctor_preservesFiniteLength _)
      (pullbackFunctor_preservesShortExact _) hl hx] at heq
  exact heq

end Preservation

end Langlands.Aubert.General
