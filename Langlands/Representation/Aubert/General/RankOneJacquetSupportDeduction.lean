import Langlands.Representation.Aubert.General.RankOneJacquetAssembly
import Langlands.Representation.Aubert.General.SupportCategoryReductions

/-! # Fixed-Levi Jacquet nonvanishing from associated support detection -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

open SmoothRep
open Langlands.Group

universe uI uG uV

section Elementary

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Each endpoint of the actual constituent sequence is an actual subquotient
of its middle representation. -/
theorem HasTwoConstituents.isSubquotient
    {E A B : SmoothRep.{0, uG, uV} ℂ G}
    (hseries : HasTwoConstituents E A B) :
    IsSubquotient A E ∧ IsSubquotient B E := by
  rcases hseries.2.2 with ⟨f, g, hex⟩ | ⟨f, g, hex⟩
  · exact ⟨IsSubrepresentation.isSubquotient ⟨ofHom f, hex.1⟩,
      IsQuotient.isSubquotient ⟨ofHom g, hex.2.1⟩⟩
  · exact ⟨IsQuotient.isSubquotient ⟨ofHom g, hex.2.1⟩,
      IsSubrepresentation.isSubquotient ⟨ofHom f, hex.1⟩⟩

end Elementary

section Standard

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- If support detection finds an associate of `I` for an irreducible
subquotient, and every other proper middle Jacquet module is zero, its detected
subset must be `I`. Properness of associates is an explicit local premise. -/
theorem jacquet_nontrivial_of_support_detection
    (hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I : Finset ι}
    (hproper : ∀ (K : Finset ι) (n : G), IsAssociate I K n → K ≠ Finset.univ)
    {E π : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hE : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E)
    (hπ : π.IsIrreducible) (hπE : IsSubquotient π E)
    (hvanish : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ I →
      IsZero ((jacquetFunctor (h K) (hU K)).obj E)) :
    Nontrivial ((jacquetFunctor (h I) (hU I)).obj π) := by
  obtain ⟨K, n, hIK, -, hnt⟩ :=
    hdet I π hπ (hE.of_isSubquotient hπE)
  have hKI : K = I := by
    by_contra hne
    have hz := (isZero_iff_subsingleton_carrier _).mp
      (hvanish K (hproper K n hIK) hne)
    exact not_subsingleton_iff_nontrivial.mpr hnt
      (jacquet_subsingleton_of_isSubquotient (h K) (hU K) (hUc K) hπE hz)
  subst K
  exact hnt

/-- Apply the fixed-Levi reduction to an irreducible actual subquotient of a
cuspidal induction, using the identity association to enter the support
category. -/
theorem jacquet_nontrivial_cuspidalInduction_subquotient_of_support_detection
    (hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {I : Finset ι} (hrefl : IsAssociate I I 1)
    (hproper : ∀ (K : Finset ι) (n : G), IsAssociate I K n → K ≠ Finset.univ)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I (hM I) (hL I) σ)
    {π : SmoothRep.{0, uG, max uG uV} ℂ G} (hπ : π.IsIrreducible)
    (hπσ : IsSubquotient π
      ((normalizedInductionFunctor (h I) (hU I)).obj σ))
    (hvanish : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ I →
      IsZero ((jacquetFunctor (h K) (hU K)).obj
        ((normalizedInductionFunctor (h I) (hU I)).obj σ))) :
    Nontrivial ((jacquetFunctor (h I) (hU I)).obj π) := by
  exact jacquet_nontrivial_of_support_detection hUc hdet hproper
    (isInSupportCategory_cuspidalInduction hrefl σ hσ hc) hπ hπσ hvanish

/-- Choose the ordered actual constituents using the supplied support
detector to establish both fixed-Levi endpoint nonvanishings. -/
def rankOneJacquetConstituentsOfSupportDetection
    (hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    {T : Subgroup G} (J : Finset ι) (hrefl : IsAssociate J J 1)
    (hproper : ∀ (K : Finset ι) (n : G), IsAssociate J K n → K ≠ Finset.univ)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU J (hM J) (hL J) σ)
    (n : RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J)
    (A B : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hseries : HasTwoConstituents
      ((normalizedInductionFunctor (h J) (hU J)).obj σ) A.val B.val)
    (hgeometry : HasRankOneJacquetMiddleSequence (h := h) (hU := hU)
      J σ n hself)
    (hvanish : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
      IsZero ((jacquetFunctor (h K) (hU K)).obj
        ((normalizedInductionFunctor (h J) (hU J)).obj σ))) :
    {ρ : FiniteLengthObject.{0, uG, max uG uV} ℂ G ×
        FiniteLengthObject.{0, uG, max uG uV} ℂ G //
      HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ)
        ρ.1.val ρ.2.val ∧
      RankOneJacquetPattern P M U h hU T J σ ρ.1.val ρ.2.val n hself} := by
  have hsub := hseries.isSubquotient
  have hA := jacquet_nontrivial_cuspidalInduction_subquotient_of_support_detection
    hUc hdet hrefl hproper σ hσ hc hseries.1 hsub.1 hvanish
  have hB := jacquet_nontrivial_cuspidalInduction_subquotient_of_support_detection
    hUc hdet hrefl hproper σ hσ hc hseries.2.1 hsub.2 hvanish
  exact rankOneJacquetConstituentsOfExactData hUc J σ hσ n hself
    A B hseries hA hB hgeometry hvanish

end Standard

end Langlands.Aubert.General
