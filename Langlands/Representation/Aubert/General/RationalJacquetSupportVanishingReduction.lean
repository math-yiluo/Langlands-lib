import Langlands.Representation.Aubert.General.JacquetSupportVanishingReduction
import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding
import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance

/-! # Full smooth support vanishing on actual rational-point families -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalSupportVanishingPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hInnerCompact : ∀ (K : Finset (SimpleRoot i ν)) (J : Finset K),
    CompactSpace (Induction.LeftQuotient
      ((parabolic i ν (leviIndex K J)).subgroupOf (levi i ν K))))

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

include hInnerCompact in
/-- Inside-Levi cuspidal embeddings, exact ambient induction and actual
induction in stages present every constituent using a subset of the coarse
index. The literal inside-Levi quotient compactness remains explicit. -/
theorem exists_induced_cuspidal_presentation_of_leviCompact
    (K : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν K))
    (hτ : τ.IsIrreducible)
    (π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hπτ : IsSubquotient π ((normalizedInductionFunctor (dec K) (hU K)).obj τ)) :
    ∃ J : Finset (SimpleRoot i ν), J ⊆ K ∧
      ∃ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J),
        σ.IsIrreducible ∧
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J
          (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ ∧
        IsSubquotient π ((normalizedInductionFunctor (dec J) (hU J)).obj σ) := by
  obtain ⟨J, σ, hσ, hcσ, hτσ⟩ :=
    exists_cuspidal_embedding_in_levi.{u, max (u + 1) v}
      i ν hInter hG hi hν hStandard hU hM K (hInnerCompact K) τ hτ
  exact ⟨leviIndex K J, leviIndex_subset K J, σ, hσ, hcσ,
    standardInduction_stages_subquotient_transitive_of_standardData.{u, v}
      i ν hStandard hG hi hν hInter hU K J (hM K) σ τ π
      hτσ.isSubquotient hπτ⟩

variable [Mono i.hom.hom.left]
  (hRoots : HasRelativeRootSystem i)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hCompact : ∀ K : Finset (SimpleRoot i ν),
    CompactSpace (Induction.LeftQuotient (parabolic i ν K)))
  (hAssoc : CuspidalSupportAssociationTarget.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (rootAssociation i ν hN hZ))

/-- A nonzero actual Jacquet module supplies a certified associated subset
on the rational-point families. Ambient and inside-Levi quotient compactness
and cuspidal-support association remain explicit. -/
def rationalAssociatedSubsetOfNonzeroJacquet
    (I K : Finset (SimpleRoot i ν))
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hE : IsInSupportCategory.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      dec hU (rootAssociation i ν hN hZ) I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) E)
    (hnonzero : Nontrivial ((jacquetFunctor (dec K) (hU K)).obj E)) :
    {p : Finset (SimpleRoot i ν) × RationalPoint k G.X //
      p.1 ⊆ K ∧ rootAssociation i ν hN hZ I p.1 p.2 ∧
      ∀ x : RationalPoint k G.X,
        x ∈ levi i ν p.1 ↔ p.2⁻¹ * x * p.2 ∈ levi i ν I} :=
  associatedSubsetOfNonzeroJacquet.{u, u, max (u + 1) v}
    hCompact
    (fun K => standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν K (hU K))
    (fun K τ hτ π _ hπτ =>
      exists_induced_cuspidal_presentation_of_leviCompact.{u, v}
        i ν hStandard hInter hG hi hν hU hM hInnerCompact K τ hτ π hπτ)
    hAssoc
    (fun _ _ _ hn hIJ σ hc =>
      isLeviCuspidal_conjugation i ν hG hi hν hStandard hInter hRoots hN hZ
        hU hM hn hIJ σ hc)
    (fun _ _ _ _ _ hIL hLJ => rootAssociation_mul i ν hN hZ hIL hLJ)
    I K E hE hnonzero

include hInnerCompact hRoots hCompact hAssoc in
/-- Full smooth Jacquet vanishing on the actual rational-point families,
conditional on actual ambient and inside-Levi quotient compactness and
cuspidal-support association. -/
theorem rationalSupportCategoryJacquetVanishing_of_compact_and_association :
    SupportCategoryJacquetVanishingTarget.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) dec hU hM
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (rootAssociation i ν hN hZ) := by
  intro I K hno E hE
  by_contra hz
  have hnonzero : Nontrivial ((jacquetFunctor (dec K) (hU K)).obj E) :=
    not_subsingleton_iff_nontrivial.mp hz
  obtain ⟨⟨J, n⟩, hJK, hIJ, hn⟩ :=
    rationalAssociatedSubsetOfNonzeroJacquet.{u, v}
      i ν hStandard hInter hG hi hν hU hM hInnerCompact
      hRoots hN hZ hCompact hAssoc I K E hE hnonzero
  exact hno J n hJK hIJ hn

end Langlands.Aubert.General.RationalPointFamily
