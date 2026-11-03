import Langlands.Representation.Aubert.General.SourceJacquetReduction
import Langlands.Representation.Aubert.General.TargetInductionReduction

/-! # Reduction of actual geometric terms to standard restricted functors -/

noncomputable section

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Conjugation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Equality identifications of the source and target commute with actual
conjugation on the full exact Grothendieck group. -/
theorem conjugationK0_subgroup_eq {S T S' T' : Subgroup G}
    (hS : S = S') (hT : T = T') (n : G)
    (h : ∀ x : G, x ∈ T ↔ n⁻¹ * x * n ∈ S)
    (h' : ∀ x : G, x ∈ T' ↔ n⁻¹ * x * n ∈ S') :
    (conjugationK0.{uG, uV} 1 (identityConjugationMembership hT)).comp
        (conjugationK0 n h) =
      (conjugationK0 n h').comp
        (conjugationK0 1 (identityConjugationMembership hS)) := by
  unfold conjugationK0
  rw [← FiniteLengthGrothendieckGroup.pullback_trans,
    ← FiniteLengthGrothendieckGroup.pullback_trans]
  congr 1
  ext x
  simp [conjugationEquiv_apply]

end Conjugation

section Terms

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))
  (I J Ks Kt : Finset ι) (n : G)
  (hKsJ : M Ks ≤ M J) (hKtI : M Kt ≤ M I)
  (hKs : IsSemidirectDecomposition
    ((P Ks).subgroupOf (M J)) ((M Ks).subgroupOf (M J)) ((U Ks).subgroupOf (M J)))
  (hKt : IsSemidirectDecomposition
    ((P Kt).subgroupOf (M I)) ((M Kt).subgroupOf (M I)) ((U Kt).subgroupOf (M I)))
  (hMem : ∀ x : G, x ∈ M Kt ↔ n⁻¹ * x * n ∈ M Ks)
  (hsfl : letI := (hM J).locallyCompactSpace
    PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} hKs
      ((hU Ks).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} hKs
      ((hU Ks).preimage continuous_subtype_val)))
  (htfl : letI := (hM I).locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} hKt
      ((hU Kt).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} hKt
      ((hU Kt).preimage continuous_subtype_val)))

/-- A term made from literal standard source restriction and target induction,
with the actual inverse-conjugation map between the two fine Levis. -/
def standardIntersectionTermK0 :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M I) :=
  letI := (hM J).locallyCompactSpace
  letI := (hM I).locallyCompactSpace
  ((FiniteLengthGrothendieckGroup.map
      (normalizedInductionFunctor hKt ((hU Kt).preimage continuous_subtype_val))
      htfl.1 htfl.2).comp
    (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hKtI))).comp
    ((conjugationK0 n hMem).comp
      ((FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hKsJ).symm).comp
        (FiniteLengthGrothendieckGroup.map
          (jacquetFunctor hKs ((hU Ks).preimage continuous_subtype_val)) hsfl.1 hsfl.2)))

variable
  (hs : GeometricSourceDecomposition P M U I J n)
  (ht : GeometricTargetDecomposition P M U I J n)
  (hSourceLevi : geometricSourceIntersection (M I) (M J) n = M Ks)
  (hSourceRadical : (geometricSourceIntersection (U I) (M J) n).subgroupOf (M J) =
    (U Ks).subgroupOf (M J))
  (hTargetLevi : geometricTargetIntersection (M I) (M J) n = M Kt)
  (hTargetParabolic : (geometricTargetIntersection (M I) (P J) n).subgroupOf (M I) =
    (P Kt).subgroupOf (M I))
  (hTargetRadical : (geometricTargetIntersection (M I) (U J) n).subgroupOf (M I) =
    (U Kt).subgroupOf (M I))

include hKsJ hKtI hKs hKt hsfl htfl hSourceLevi hSourceRadical
  hTargetLevi hTargetParabolic hTargetRadical in
/-- Preservation for both actual factors follows from the standard restricted
functors and the displayed subgroup identities. -/
theorem geometricTermFiniteLengthOfEq :
    GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht := by
  have hs' := geometricSourceJacquetPreservationOfEq.{uI, uG, max uG uV}
    P M U hM hU I J Ks n hs hKsJ hKs hSourceLevi hSourceRadical hsfl
  have ht' := geometricTargetInductionPreservationOfEq.{uI, uG, max uG uV}
    P M U hM hU I J Kt n ht hKtI hKt hTargetLevi hTargetParabolic hTargetRadical htfl
  exact ⟨hs'.1, hs'.2, ht'.1, ht'.2⟩

include hKsJ hKtI hKs hKt hMem hsfl htfl hSourceLevi hSourceRadical
  hTargetLevi hTargetParabolic hTargetRadical in
/-- Every actual geometric term is the term of literal standard restricted
functors once the subgroup identities are supplied. Preservation witnesses
for the actual term may be arbitrary. -/
theorem geometricTermK0_eq_standardOfEq
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht) :
    geometricTermK0.{uI, uG, uV} P M U hM hU I J n hs ht hfl =
      standardIntersectionTermK0.{uI, uG, uV}
        P M U hM hU I J Ks Kt n hKsJ hKtI hKs hKt hMem hsfl htfl := by
  let _ := (hM J).locallyCompactSpace
  let _ := (hM I).locallyCompactSpace
  have hsrc := geometricSourceJacquetK0OfEq.{uI, uG, max uG uV}
    P M U hM hU I J Ks n hs hKsJ hKs hSourceLevi hSourceRadical hsfl
  have htgt := geometricTargetInductionK0OfEq.{uI, uG, max uG uV}
    P M U hM hU I J Kt n ht hKtI hKt hTargetLevi hTargetParabolic hTargetRadical htfl
  change (geometricTargetInductionK0 P M U hM hU I J Kt n ht hKtI hKt
      hTargetLevi hTargetParabolic hTargetRadical htfl).comp
      ((conjugationK0 n (geometricIntersectionMembership (M I) (M J) n)).comp
        (geometricSourceJacquetK0 P M U hM hU I J Ks n hs hKsJ hKs
          hSourceLevi hSourceRadical hsfl)) = _
  rw [htgt]
  apply LinearMap.ext
  intro x
  have hc := LinearMap.congr_fun
    (conjugationK0_subgroup_eq.{uG, max uG uV} hSourceLevi hTargetLevi n
      (geometricIntersectionMembership (M I) (M J) n) hMem)
    ((geometricSourceJacquetK0 P M U hM hU I J Ks n hs hKsJ hKs
      hSourceLevi hSourceRadical hsfl) x)
  have hsrcx := LinearMap.congr_fun hsrc x
  simp only [LinearMap.comp_apply] at hc hsrcx
  simp only [standardIntersectionTermK0, LinearMap.comp_apply]
  rw [hc, hsrcx]

end Terms

end Langlands.Aubert.General
