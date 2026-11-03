import Langlands.Representation.Aubert.General.SourceJacquetComparison

/-! # Standardizing actual target-intersection induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {M Q L N Q' L' N' : Subgroup G}

private theorem normalizedInductionFunctor_eq_of_subgroups_eq
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P P' A V V' : Subgroup H}
    (h : IsSemidirectDecomposition P A V)
    (h' : IsSemidirectDecomposition P' A V')
    (hV : IsClosed (V : Set H)) (hV' : IsClosed (V' : Set H))
    (hPP' : P = P') (hVV' : V = V') :
    normalizedInductionFunctor.{uG, uV} h hV =
      normalizedInductionFunctor h' hV' := by
  subst P' V'
  rfl

/-- Equal ambient Levis and equal parabolic/radical subgroups inside the coarse
Levi identify the actual normalized induction functors. -/
def leviNormalizedInductionIsoOfEq
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M) (hL'M : L' ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (h' : IsSemidirectDecomposition
      (Q'.subgroupOf M) (L'.subgroupOf M) (N'.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hN' : IsClosed (N' : Set G))
    (hLL' : L = L') (hQQ' : Q.subgroupOf M = Q'.subgroupOf M)
    (hNN' : N.subgroupOf M = N'.subgroupOf M) :
    conjugationFunctor.{uG, uV} 1 (identityConjugationMembership hLL') ⋙
        leviNormalizedInductionFunctor hM hL'M h' hN' ≅
      leviNormalizedInductionFunctor hM hLM h hN := by
  subst L'
  letI := hM.locallyCompactSpace
  have hInd := normalizedInductionFunctor_eq_of_subgroups_eq h h'
    (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val)
    hQQ' hNN'
  change conjugationFunctor 1 (identityConjugationMembership rfl) ⋙
      (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM) ⋙
        normalizedInductionFunctor _ _) ≅
    SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM) ⋙
      normalizedInductionFunctor _ _
  rw [hInd]
  exact Functor.isoWhiskerRight (conjugationFunctorOneNatIso _) _ ≪≫
    Functor.leftUnitor _

end Levi

section GeometricTarget

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- The actual target-intersection induction is the literal standard induction
after identity identification of the Levi, under the displayed subgroup
equalities. The structural equalities remain explicit inputs. -/
def geometricTargetInductionComparisonIso
    (I J K : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hKI : M K ≤ M I)
    (hK : IsSemidirectDecomposition
      ((P K).subgroupOf (M I)) ((M K).subgroupOf (M I)) ((U K).subgroupOf (M I)))
    (hLevi : geometricTargetIntersection (M I) (M J) n = M K)
    (hParabolic : (geometricTargetIntersection (M I) (P J) n).subgroupOf (M I) =
      (P K).subgroupOf (M I))
    (hRadical : (geometricTargetIntersection (M I) (U J) n).subgroupOf (M I) =
      (U K).subgroupOf (M I)) :
    conjugationFunctor.{uG, uV} 1 (identityConjugationMembership hLevi) ⋙
        leviNormalizedInductionFunctor (hM I) hKI hK (hU K) ≅
      geometricTargetInductionFunctor P M U hM hU I J n ht :=
  leviNormalizedInductionIsoOfEq (hM I) inf_le_left hKI ht hK
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)
    (hU K) hLevi hParabolic hRadical

end GeometricTarget

end Langlands.Aubert.General
