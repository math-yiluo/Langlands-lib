import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.Aubert.General.Parabolic

/-! Conditional Jacquet-lemma and admissibility propositions on the actual quotients. -/

namespace Langlands.Jacquet

universe uG uV

/-- The actual quotient map on fixed vectors is surjective under explicit
factorization, contraction and finite-dimensionality hypotheses. -/
def IwahoriContractionJacquetLemmaStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (_hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (_hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (g : G),
    IsIwahoriContraction K N M Nbar g →
      ∀ hMN : M ≤ Subgroup.normalizer N,
        FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) →
          Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup)

/-- The generalized kernel of compression is the kernel of the restricted
actual quotient map. No finite-dimensionality hypothesis is imposed. -/
def IwahoriContractionKernelStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (g : G),
    IsIwahoriContraction K N M Nbar g →
      ∀ hMN : M ≤ Subgroup.normalizer N,
        powerKernelSup ρ hρ K hK g =
          LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup)

/-- The actual quotient map is bijective on the stable image of compression,
under finite-dimensionality of the fixed-vector space. -/
def IwahoriContractionStableImageStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (g : G),
    IsIwahoriContraction K N M Nbar g →
      ∀ hMN : M ≤ Subgroup.normalizer N,
        FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) →
          Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN)

/-- The actual unnormalized Jacquet action is admissible under the explicit
cofinal compact-open contraction hypothesis. -/
def IwahoriContractionAdmissibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N M Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N),
    HasIwahoriContractionBasis N M Nbar → IsAdmissible ρ →
      IsAdmissible (action ρ N M hMN)

/-- The actual intrinsically normalized Jacquet functor preserves admissibility
under the same explicit cofinal contraction condition. -/
def IwahoriContractionNormalizedAdmissibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    [NonarchimedeanGroup G] (N M Nbar : Subgroup G)
    (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer (N : Set G)),
    HasIwahoriContractionBasis N M Nbar →
      ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsAdmissible →
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).IsAdmissible

/-- The conditional weak Jacquet lemma, its generalized kernel/stable-image
refinement, and the unnormalized and normalized admissibility corollaries. -/
def IwahoriContractionJacquetStatement : Prop :=
  IwahoriContractionJacquetLemmaStatement.{uG, uV} ∧
    IwahoriContractionKernelStatement.{uG, uV} ∧
    IwahoriContractionStableImageStatement.{uG, uV} ∧
    IwahoriContractionAdmissibilityStatement.{uG, uV} ∧
    IwahoriContractionNormalizedAdmissibilityStatement.{uG, uV}

end Langlands.Jacquet
