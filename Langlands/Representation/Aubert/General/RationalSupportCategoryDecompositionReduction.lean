import Langlands.Representation.Aubert.General.SupportCategoryDecompositionReduction
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance

/-! # The actual rational support decomposition from embedding, induced support and association -/

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

section Association

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- Existence of an actual root-association representative is an equivalence
relation on the finite sets of simple roots. -/
def rootAssociationSetoid : Setoid (Finset (SimpleRoot i ν)) where
  r I J := ∃ n, rootAssociation i ν hN hZ I J n
  iseqv :=
    ⟨fun I => ⟨1, rootAssociation_one i ν hN hZ I⟩,
      fun ⟨n, hn⟩ => ⟨n⁻¹, rootAssociation_inv i ν hN hZ hn⟩,
      fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨m * n, rootAssociation_mul i ν hN hZ hn hm⟩⟩

end Association

/-- Renard, Théorème VI.7.2, on the actual families, grouped by association
classes of standard Levis: the actual support decomposition follows from the
finite induced-cuspidal embedding, the support of induced inside-Levi cuspidal
objects and the association of cuspidal data. Association invariance of the
support categories is the proved `rationalSupportCategoryAssociationInvariance`. -/
theorem rationalSupportCategoryDecomposition_of_inducedCuspidal
    (hEmb : RationalCuspidalInducedEmbeddingStatement.{u, max (u + 1) v})
    (hInd : RationalInducedCuspidalSupportCategoryStatement.{u, v})
    (hAssoc : RationalCuspidalSupportAssociationStatement.{u, v}) :
    RationalSupportCategoryDecompositionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact supportCategoryDecomposition_of_inducedEmbedding
    (rootAssociationSetoid i ν hN hZ)
    (fun I J ⟨n, hn⟩ E hE => rationalSupportCategoryAssociationInvariance k G hG T i hi ν hν
      hStandard hInter hRoots hN hZ hU hM I J n hn
      (rootAssociation_levi_membership i ν hN hZ hG hi hν hStandard hn) E hE)
    (fun I J π hπ hπI hπJ => exists_isAssociate_of_isInSupportCategory
      (hAssoc k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
      (fun I J n hn hIJ σ hc => isLeviCuspidal_conjugation i ν hG hi hν hStandard hInter
        hRoots hN hZ hU hM hn hIJ σ hc)
      (fun I J n hIJ => rootAssociation_inv i ν hN hZ hIJ)
      (fun I K J n m hIK hKJ => rootAssociation_mul i ν hN hZ hIK hKJ) hπ hπI hπJ)
    (hInd k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    (hEmb k G hG T i hi ν hν hStandard hInter hRoots hU hM)

end Langlands.Aubert.General.RationalPointFamily
