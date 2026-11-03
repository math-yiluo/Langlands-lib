import Langlands.Representation.Aubert.General.SupportCategoryStatements

/-! # Irreducible Jacquet detection from cuspidal realizations and association -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- Choose an associated standard Levi with nonzero actual Jacquet module.
The inputs supply a cuspidal realization with nonzero Jacquet module, association
of cuspidal supports, transport of cuspidality, and composition of the actual
association representatives. The returned point is their literal product. -/
def associatedJacquetWitnessOfCuspidalRealizations
    (hrealize : ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
      ∃ (J : Finset ι) (τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)),
        τ.IsIrreducible ∧ IsLeviCuspidal P M U hU J (hM J) (hL J) τ ∧
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj τ) ∧
        Nontrivial ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj π))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset ι) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I K J : Finset ι) (n m : G),
      IsAssociate I K n → IsAssociate K J m → IsAssociate I J (m * n))
    (I : Finset ι) (π : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hπ : π.IsIrreducible)
    (hπI : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π) :
    {p : Finset ι × G //
      IsAssociate I p.1 p.2 ∧
      (∀ x : G, x ∈ M p.1 ↔ p.2⁻¹ * x * p.2 ∈ M I) ∧
      Nontrivial ((jacquetFunctor.{uG, max uG uV} (h p.1) (hU p.1)).obj π)} := by
  apply Classical.choice
  obtain ⟨J, τ, hτ, hcτ, hπτ, hJ⟩ := hrealize π hπ
  have hππ : SmoothRep.IsSubquotient π π :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨π, 𝟙 π, 𝟙 π, fun _ _ hxy => hxy, fun x => ⟨x, rfl⟩⟩
  obtain ⟨K, n, hn, hIK, σ, hσ, hcσ, hπσ⟩ :=
    hπI π hπ hππ
  have hσn : ((conjugationFunctor n hn).obj σ).IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff
      σ.representation (conjugationEquiv n hn)).mpr hσ
  obtain ⟨m, hm, hKJ, _⟩ :=
    hassoc π hπ K J ((conjugationFunctor n hn).obj σ) τ
      hσn (hconjCusp I K n hn hIK σ hcσ) hτ hcτ hπσ hπτ
  refine ⟨⟨(J, m * n), hcomp I K J n m hIK hKJ, ?_, hJ⟩⟩
  intro x
  simpa only [mul_inv_rev, mul_assoc] using
    (hm x).trans (hn (m⁻¹ * x * m))

/-- The generic irreducible detection target follows from the four explicit
inputs to `associatedJacquetWitnessOfCuspidalRealizations`. No realization,
support-association or cuspidality-transport theorem is asserted by this
conditional reduction. -/
theorem supportCategoryIrreducibleJacquetDetection_of_cuspidalRealizations
    (hrealize : ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
      ∃ (J : Finset ι) (τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)),
        τ.IsIrreducible ∧ IsLeviCuspidal P M U hU J (hM J) (hL J) τ ∧
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj τ) ∧
        Nontrivial ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj π))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset ι) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I K J : Finset ι) (n m : G),
      IsAssociate I K n → IsAssociate K J m → IsAssociate I J (m * n)) :
    SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate := by
  intro I π hπ hπI
  obtain ⟨⟨J, n⟩, hn⟩ :=
    associatedJacquetWitnessOfCuspidalRealizations hrealize hassoc hconjCusp hcomp I π hπ hπI
  exact ⟨J, n, hn⟩

end Langlands.Aubert.General
