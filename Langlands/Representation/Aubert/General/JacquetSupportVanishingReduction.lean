import Langlands.Representation.Aubert.General.JacquetCommonConstituent
import Langlands.Representation.Aubert.General.SupportCategoryStatements
import Langlands.Representation.Aubert.General.ConjugationComposition

/-! # Full smooth support vanishing from common-constituent presentations -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {ι : Type uI}
  {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I))
      ((U (leviIndex I J)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- A nonzero Jacquet module of a support-category object supplies an actual
associated subset of `K`. Every structural and cuspidal-presentation input
remains explicit. The witness retains the same product point in association
and subgroup membership. -/
def associatedSubsetOfNonzeroJacquet
    (hcompact : ∀ K, CompactSpace (Induction.LeftQuotient (P K)))
    (hδ : ∀ K, IsUnimodularModulus (U K) (hU K))
    (hpresent : ∀ (K : Finset ι)
      (τ : SmoothRep.{0, uG, max uG uV} ℂ (M K)), τ.IsIrreducible →
      ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor (h K) (hU K)).obj τ) →
        ∃ (J : Finset ι), J ⊆ K ∧
          ∃ σ : SmoothRep.{0, uG, max uG uV} ℂ (M J),
            σ.IsIrreducible ∧ IsLeviCuspidal P M U hU J (hM J) (hL J) σ ∧
            SmoothRep.IsSubquotient π
              ((normalizedInductionFunctor (h J) (hU J)).obj σ))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset ι) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I L J : Finset ι) (n m : G),
      IsAssociate I L n → IsAssociate L J m → IsAssociate I J (m * n))
    (I K : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hE : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E)
    (hnonzero : Nontrivial ((jacquetFunctor (h K) (hU K)).obj E)) :
    {p : Finset ι × G // p.1 ⊆ K ∧ IsAssociate I p.1 p.2 ∧
      ∀ x : G, x ∈ M p.1 ↔ p.2⁻¹ * x * p.2 ∈ M I} := by
  apply Classical.choice
  let := hcompact K
  let c := JacquetCommonConstituent.of_nontrivial_jacquet
    (h K) (hU K) (hδ K) E hnonzero
  obtain ⟨J, hJK, τ, hτ, hcτ, hπτ⟩ :=
    hpresent K c.levi c.levi_irreducible
      c.constituent c.constituent_irreducible c.subquotient_induced
  obtain ⟨L, n, hn, hIL, σ, hσ, hcσ, hπσ⟩ :=
    hE c.constituent c.constituent_irreducible c.subquotient_original
  have hσn : ((conjugationFunctor n hn).obj σ).IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff
      σ.representation (conjugationEquiv n hn)).mpr hσ
  obtain ⟨m, hm, hLJ, _⟩ :=
    hassoc c.constituent c.constituent_irreducible
      L J ((conjugationFunctor n hn).obj σ) τ
      hσn (hconjCusp I L n hn hIL σ hcσ) hτ hcτ hπσ hπτ
  exact ⟨⟨(J, m * n), hJK, hcomp I L J n m hIL hLJ,
    conjugationMembership_mul n m hn hm⟩⟩

/-- For arbitrary smooth objects, compact actual parabolic quotients and
unimodularity reduce support-category Jacquet vanishing to cuspidal
presentations of induced irreducible constituents, association of cuspidal
supports, transport of cuspidality and composition of actual representatives.
All of these inputs remain explicit. -/
theorem supportCategoryJacquetVanishing_of_inducedCuspidalPresentations
    (hcompact : ∀ K, CompactSpace (Induction.LeftQuotient (P K)))
    (hδ : ∀ K, IsUnimodularModulus (U K) (hU K))
    (hpresent : ∀ (K : Finset ι)
      (τ : SmoothRep.{0, uG, max uG uV} ℂ (M K)), τ.IsIrreducible →
      ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor (h K) (hU K)).obj τ) →
        ∃ (J : Finset ι), J ⊆ K ∧
          ∃ σ : SmoothRep.{0, uG, max uG uV} ℂ (M J),
            σ.IsIrreducible ∧ IsLeviCuspidal P M U hU J (hM J) (hL J) σ ∧
            SmoothRep.IsSubquotient π
              ((normalizedInductionFunctor (h J) (hU J)).obj σ))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset ι) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I L J : Finset ι) (n m : G),
      IsAssociate I L n → IsAssociate L J m → IsAssociate I J (m * n)) :
    SupportCategoryJacquetVanishingTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate := by
  intro I K hno E hE
  by_contra hz
  have hnonzero : Nontrivial ((jacquetFunctor (h K) (hU K)).obj E) :=
    not_subsingleton_iff_nontrivial.mp hz
  obtain ⟨⟨J, n⟩, hJK, hIJ, hn⟩ :=
    associatedSubsetOfNonzeroJacquet hcompact hδ hpresent hassoc hconjCusp hcomp
      I K E hE hnonzero
  exact hno J n hJK hIJ hn

end Langlands.Aubert.General
