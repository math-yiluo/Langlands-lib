import Langlands.Representation.Aubert.General.ConjugationComposition
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget

/-! # Association through one common actual cuspidal Jacquet factor -/

noncomputable section

open CategoryTheory

universe uI uG uV

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

omit [LocallyCompactSpace G] in
/-- Compare two data conjugate to one common datum by the actual
inverse/product representative, retaining its explicit membership witness. -/
def conjugationDataIsoOfCommonConjugate
    {I I' J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {σ' : SmoothRep.{0, uG, max uG uV} ℂ (M I')}
    {τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {n₁ n₂ : G}
    (hn₁ : ∀ x : G, x ∈ M J ↔ n₁⁻¹ * x * n₁ ∈ M I)
    (hn₂ : ∀ x : G, x ∈ M J ↔ n₂⁻¹ * x * n₂ ∈ M I')
    (e₁ : τ ≅ (conjugationFunctor n₁ hn₁).obj σ)
    (e₂ : τ ≅ (conjugationFunctor n₂ hn₂).obj σ') :
    σ' ≅ (conjugationFunctor (n₂⁻¹ * n₁)
      (conjugationMembership_mul n₁ n₂⁻¹ hn₁
        (conjugationMembership_inv n₂ hn₂))).obj σ :=
  conjugationDataIsoTrans n₁ n₂⁻¹ hn₁
    (conjugationMembership_inv n₂ hn₂) e₁
    (conjugationDataIsoSymm n₂ hn₂ e₂)

omit [LocallyCompactSpace G] in
/-- Reverse one of two actual associations to a common datum and compose it
with the other. The same product represents all three comparisons. -/
theorem associatedData_of_common_conjugate
    (hInv : ∀ {I J : Finset ι} {n : G},
      IsAssociate I J n → IsAssociate J I n⁻¹)
    (hMul : ∀ {I J K : Finset ι} {n m : G},
      IsAssociate I J n → IsAssociate J K m → IsAssociate I K (m * n))
    {I I' J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {σ' : SmoothRep.{0, uG, max uG uV} ℂ (M I')}
    {τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {n₁ n₂ : G}
    (hn₁ : ∀ x : G, x ∈ M J ↔ n₁⁻¹ * x * n₁ ∈ M I)
    (hn₂ : ∀ x : G, x ∈ M J ↔ n₂⁻¹ * x * n₂ ∈ M I')
    (hIJ : IsAssociate I J n₁) (hI'J : IsAssociate I' J n₂)
    (e₁ : τ ≅ (conjugationFunctor n₁ hn₁).obj σ)
    (e₂ : τ ≅ (conjugationFunctor n₂ hn₂).obj σ') :
    ∃ hn : ∀ x : G, x ∈ M I' ↔ (n₂⁻¹ * n₁)⁻¹ * x * (n₂⁻¹ * n₁) ∈ M I,
      IsAssociate I I' (n₂⁻¹ * n₁) ∧
        Nonempty (σ' ≅ (conjugationFunctor (n₂⁻¹ * n₁) hn).obj σ) := by
  refine ⟨conjugationMembership_mul n₁ n₂⁻¹ hn₁
    (conjugationMembership_inv n₂ hn₂), hMul hIJ (hInv hI'J), ?_⟩
  exact ⟨conjugationDataIsoOfCommonConjugate M hn₁ hn₂ e₁ e₂⟩

/-- Extract the same actual cuspidal Jacquet factor from two inducing data,
then associate those data with one inverse/product representative. -/
theorem associatedData_of_cuspidalJacquetFactor
    (hExtract : CuspidalJacquetFactorExtractionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hInv : ∀ {I J : Finset ι} {n : G},
      IsAssociate I J n → IsAssociate J I n⁻¹)
    (hMul : ∀ {I J K : Finset ι} {n m : G},
      IsAssociate I J n → IsAssociate J K m → IsAssociate I K (m * n))
    {π : SmoothRep.{0, uG, max uG uV} ℂ G}
    {I I' J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {σ' : SmoothRep.{0, uG, max uG uV} ℂ (M I')}
    {τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    (hσ : σ.IsIrreducible) (hcσ : IsLeviCuspidal P M U hU I (hM I) (hL I) σ)
    (hσ' : σ'.IsIrreducible) (hcσ' : IsLeviCuspidal P M U hU I' (hM I') (hL I') σ')
    (hτ : τ.IsIrreducible) (hcτ : IsLeviCuspidal P M U hU J (hM J) (hL J) τ)
    (hπ : SmoothRep.IsSubquotient π ((normalizedInductionFunctor (h I) (hU I)).obj σ))
    (hπ' : SmoothRep.IsSubquotient π ((normalizedInductionFunctor (h I') (hU I')).obj σ'))
    (hτπ : SmoothRep.IsSubquotient τ ((jacquetFunctor (h J) (hU J)).obj π)) :
    ∃ (n : G) (hn : ∀ x : G, x ∈ M I' ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I I' n ∧ Nonempty (σ' ≅ (conjugationFunctor n hn).obj σ) := by
  obtain ⟨n₁, hn₁, hIJ, ⟨e₁⟩⟩ :=
    hExtract I J σ π τ hσ hcσ hτ hcτ hπ hτπ
  obtain ⟨n₂, hn₂, hI'J, ⟨e₂⟩⟩ :=
    hExtract I' J σ' π τ hσ' hcσ' hτ hcτ hπ' hτπ
  obtain ⟨hn, hII', e⟩ :=
    associatedData_of_common_conjugate M IsAssociate hInv hMul hn₁ hn₂ hIJ hI'J e₁ e₂
  exact ⟨n₂⁻¹ * n₁, hn, hII', e⟩

/-- A common actual cuspidal Jacquet factor for each irreducible, together
with the extraction theorem, suffices for the full association target.
No induction realization of the common Jacquet factor is needed. -/
theorem cuspidalSupportAssociationTarget_of_cuspidalJacquetFactors
    (hExtract : CuspidalJacquetFactorExtractionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hInv : ∀ {I J : Finset ι} {n : G},
      IsAssociate I J n → IsAssociate J I n⁻¹)
    (hMul : ∀ {I J K : Finset ι} {n m : G},
      IsAssociate I J n → IsAssociate J K m → IsAssociate I K (m * n))
    (hFactor : ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
      ∃ (J : Finset ι) (τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)),
        τ.IsIrreducible ∧ IsLeviCuspidal P M U hU J (hM J) (hL J) τ ∧
          SmoothRep.IsSubquotient τ ((jacquetFunctor (h J) (hU J)).obj π)) :
    CuspidalSupportAssociationTarget.{uI, uG, uV} P M U h hU hM hL IsAssociate := by
  intro π hπirr I I' σ σ' hσ hcσ hσ' hcσ' hπ hπ'
  obtain ⟨J, τ, hτ, hcτ, hτπ⟩ := hFactor π hπirr
  exact associatedData_of_cuspidalJacquetFactor P M U h hU hM hL IsAssociate
    hExtract hInv hMul hσ hcσ hσ' hcσ' hτ hcτ hπ hπ' hτπ

end Langlands.Aubert.General
