import Langlands.Representation.Aubert.General.GeometricTermReduction
import Langlands.Representation.Aubert.General.InductionK0Stages
import Langlands.Representation.Aubert.General.InductionK0Assembly
import Langlands.Representation.Aubert.GeneralWeylConjugacyTarget

/-! # Induced standard intersection terms on exact K0 -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {ι : Type uI}
  (P M U : Finset ι → Subgroup G)
  (h : ∀ K, IsSemidirectDecomposition (P K) (M K) (U K))
  (hU : ∀ K, IsClosed (U K : Set G))
  (hfl : ∀ K, ParabolicFiniteLength.{uG, max uG uV} (h K) (hU K))
  (hM : ∀ K, IsClosed (M K : Set G))
  (I J : Finset ι) (Ks : Finset J) (Kt : Finset I) (n : G)
  (hKsJ : M (leviIndex J Ks) ≤ M J)
  (hKtI : M (leviIndex I Kt) ≤ M I)
  (hJ : ∀ K : Finset J, IsSemidirectDecomposition
    ((P (leviIndex J K)).subgroupOf (M J))
    ((M (leviIndex J K)).subgroupOf (M J))
    ((U (leviIndex J K)).subgroupOf (M J)))
  (hKt : IsSemidirectDecomposition
    ((P (leviIndex I Kt)).subgroupOf (M I))
    ((M (leviIndex I Kt)).subgroupOf (M I))
    ((U (leviIndex I Kt)).subgroupOf (M I)))
  (hMem : ∀ x : G, x ∈ M (leviIndex I Kt) ↔
    n⁻¹ * x * n ∈ M (leviIndex J Ks))
  (hLfl : letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val))
  (htfl : letI := (hM I).locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV}
      hKt ((hU (leviIndex I Kt)).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV}
      hKt ((hU (leviIndex I Kt)).preimage continuous_subtype_val)))

/-- Ambient induction of the standard restricted intersection term, retaining
the actual fine-Levi inverse conjugation. -/
def inducedStandardIntersectionTermK0 :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  letI := (hM J).locallyCompactSpace
  (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1).comp
    (standardIntersectionTermK0.{uI, uG, uV} P M U hM hU
      I J (leviIndex J Ks) (leviIndex I Kt) n hKsJ hKtI (hJ Ks) hKt hMem
      ⟨(hLfl Ks).2.2.1, (hLfl Ks).2.2.2⟩ htfl)

variable
  (hSourceStages : leviNormalizedInductionFunctor.{uG, max uG uV}
      (hM J) hKsJ (hJ Ks) (hU (leviIndex J Ks)) ⋙
        normalizedInductionFunctor (h J) (hU J) ≅
      normalizedInductionFunctor (h (leviIndex J Ks)) (hU (leviIndex J Ks)))
  (hTargetStages : leviNormalizedInductionFunctor.{uG, max uG uV}
      (hM I) hKtI hKt (hU (leviIndex I Kt)) ⋙
        normalizedInductionFunctor (h I) (hU I) ≅
      normalizedInductionFunctor (h (leviIndex I Kt)) (hU (leviIndex I Kt)))
  (hWeyl :
    (inductionK0.{uG, uV}
      (h (leviIndex I Kt)) (hU (leviIndex I Kt))
      (hfl (leviIndex I Kt)).1 (hfl (leviIndex I Kt)).2.1).comp
        (conjugationK0.{uG, max uG uV} n hMem) =
      inductionK0 (h (leviIndex J Ks)) (hU (leviIndex J Ks))
        (hfl (leviIndex J Ks)).1 (hfl (leviIndex J Ks)).2.1)

include hSourceStages hTargetStages hWeyl in
/-- Actual stages on both sides and fine-Levi induced Weyl equality reduce the
whole induced standard intersection term to its source alternating term. -/
theorem inducedStandardIntersectionTermK0_eq :
    inducedStandardIntersectionTermK0.{uI, uG, uV}
      P M U h hU hfl hM I J Ks Kt n hKsJ hKtI hJ hKt hMem hLfl htfl =
    inducedLeviAlternatingTerm.{uI, uG, uV}
      P M U h hU hfl hM J hJ hLfl Ks := by
  let _ := (hM J).locallyCompactSpace
  let _ := (hM I).locallyCompactSpace
  have hT := inductionK0_comp_leviInductionK0.{uG, uV}
    (h (leviIndex I Kt)) (h I) (hM I) hKtI hKt
    (hU (leviIndex I Kt)) (hU I) htfl
    ⟨(hfl (leviIndex I Kt)).1, (hfl (leviIndex I Kt)).2.1⟩
    ⟨(hfl I).1, (hfl I).2.1⟩ hTargetStages
  have hS := inductionK0_comp_restrictedInductionK0.{uG, uV}
    (h (leviIndex J Ks)) (h J) (hM J) hKsJ (hJ Ks)
    (hU (leviIndex J Ks)) (hU J)
    ⟨(hLfl Ks).1, (hLfl Ks).2.1⟩
    ⟨(hfl (leviIndex J Ks)).1, (hfl (leviIndex J Ks)).2.1⟩
    ⟨(hfl J).1, (hfl J).2.1⟩ hSourceStages
  change
    (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1).comp
      ((leviInductionK0.{uG, uV} (hM I) hKtI hKt (hU (leviIndex I Kt)) htfl).comp
        ((conjugationK0 n hMem).comp
          ((FiniteLengthGrothendieckGroup.pullback
            (subgroupOfContinuousEquiv hKsJ).symm).comp
            (jacquetK0 (hJ Ks) ((hU (leviIndex J Ks)).preimage continuous_subtype_val)
              (hLfl Ks).2.2.1 (hLfl Ks).2.2.2)))) =
      (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
        ((inductionK0 (hJ Ks) ((hU (leviIndex J Ks)).preimage continuous_subtype_val)
          (hLfl Ks).1 (hLfl Ks).2.1).comp
            (jacquetK0 (hJ Ks) ((hU (leviIndex J Ks)).preimage continuous_subtype_val)
              (hLfl Ks).2.2.1 (hLfl Ks).2.2.2))
  rw [← LinearMap.comp_assoc, hT, ← LinearMap.comp_assoc, hWeyl]
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, hS]

end Langlands.Aubert.General
