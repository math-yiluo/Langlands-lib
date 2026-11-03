import Langlands.Representation.Aubert.General.TwoJacquetFactors
import Langlands.Representation.Aubert.General.SupportCategoryReductions

/-! # Two possibly different Jacquet detectors from associated support -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {ι : Type uI}
  {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- If the associates of `I` have only two possible indices, associated
support detection detects an irreducible subquotient at one of those two
indices. No normalization or equality of the two Levis is required. -/
theorem two_jacquet_nontrivial_of_support_detection
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I J : Finset ι}
    (htwo : ∀ (K : Finset ι) (n : G), IsAssociate I K n → K = I ∨ K = J)
    {E π : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hE : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E)
    (hπ : π.IsIrreducible) (hπE : IsSubquotient π E) :
    Nontrivial ((jacquetFunctor (h I) (hU I)).obj π) ∨
      Nontrivial ((jacquetFunctor (h J) (hU J)).obj π) := by
  obtain ⟨K, n, hIK, -, hnt⟩ :=
    hdet I π hπ (hE.of_isSubquotient hπE)
  rcases htwo K n hIK with rfl | rfl
  · exact Or.inl hnt
  · exact Or.inr hnt

/-- Apply the two-index support detector to the actual induction of an
irreducible cuspidal object, without a finite-length premise. -/
theorem two_jacquet_nontrivial_cuspidalInduction_subquotient
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I J : Finset ι} (hrefl : IsAssociate I I 1)
    (htwo : ∀ (K : Finset ι) (n : G), IsAssociate I K n → K = I ∨ K = J)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I (hM I) (hL I) σ)
    {π : SmoothRep.{0, uG, max uG uV} ℂ G} (hπ : π.IsIrreducible)
    (hπσ : IsSubquotient π ((normalizedInductionFunctor (h I) (hU I)).obj σ)) :
    Nontrivial ((jacquetFunctor (h I) (hU I)).obj π) ∨
      Nontrivial ((jacquetFunctor (h J) (hU J)).obj π) :=
  two_jacquet_nontrivial_of_support_detection hdet htwo
    (isInSupportCategory_cuspidalInduction hrefl σ hσ hc) hπ hπσ

/-- Choose the actual two factors and their asymmetric Jacquet pattern
from associated support detection at two possible indices and two simple
middle Jacquet modules. The indices may be different. -/
def inductionTwoJacquetFactorsOfSupportDetection
    (hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I J : Finset ι} (hrefl : IsAssociate I I 1)
    (htwo : ∀ (K : Finset ι) (n : G), IsAssociate I K n → K = I ∨ K = J)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I (hM I) (hL I) σ)
    (hJac : ((jacquetFunctor (h I) (hU I)).obj
      ((normalizedInductionFunctor (h I) (hU I)).obj σ)).IsIrreducible)
    (hJacJ : ((jacquetFunctor (h J) (hU J)).obj
      ((normalizedInductionFunctor (h I) (hU I)).obj σ)).IsIrreducible)
    (hred : ¬ ((normalizedInductionFunctor (h I) (hU I)).obj σ).IsIrreducible) :
    InductionTwoJacquetFactors (h I) (hU I) (h J) (hU J) σ :=
  inductionTwoJacquetFactors (h I) (hU I) (hUc I) (h J) (hU J) (hUc J) σ
    hJac hJacJ
    (fun _ hπ hπσ => two_jacquet_nontrivial_cuspidalInduction_subquotient
      hdet hrefl htwo σ hσ hc hπ hπσ) hσ hred

/-- Vanishing of any other actual Jacquet module of the induction passes
to both literal factors in the constructed short exact sequence. -/
theorem InductionTwoJacquetFactors.other_jacquet_subsingleton
    {I J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    (F : InductionTwoJacquetFactors (h I) (hU I) (h J) (hU J) σ)
    (K : Finset ι) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hzero : Subsingleton ((jacquetFunctor (h K) (hU K)).obj
      ((normalizedInductionFunctor (h I) (hU I)).obj σ))) :
    Subsingleton ((jacquetFunctor (h K) (hU K)).obj
      (subrepresentation ((normalizedInductionFunctor (h I) (hU I)).obj σ) F.subspace)) ∧
    Subsingleton ((jacquetFunctor (h K) (hU K)).obj
      (quotient ((normalizedInductionFunctor (h I) (hU I)).obj σ) F.subspace)) := by
  let A := (normalizedInductionFunctor (h I) (hU I)).obj σ
  exact
    ⟨jacquet_subsingleton_of_isSubquotient (h K) (hU K) hUc
      (IsSubrepresentation.isSubquotient ⟨subtype A F.subspace,
        subtype_injective A F.subspace⟩) hzero,
      jacquet_subsingleton_of_isSubquotient (h K) (hU K) hUc
        (IsQuotient.isSubquotient ⟨mkQ A F.subspace, mkQ_surjective A F.subspace⟩) hzero⟩

end Langlands.Aubert.General
