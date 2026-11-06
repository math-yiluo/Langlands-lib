import Langlands.GroupScheme.SimplyConnected.DirectFactors
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementStatement

/-! # Simple connectedness of normal subgroups from normal complements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Normal semisimple complements imply simple connectedness of every smooth
connected closed normal subgroup of a simply connected group. -/
theorem IsSimplyConnected.normalSubgroup_of_normalIsogenyComplement
    (hG : IsSimplyConnected G)
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (hn : (SubgroupFunctor.range j).IsNormal) : IsSimplyConnected H := by
  obtain ⟨hH, K, i, hK, _hi, _hnK, hprod, hcomm, hm⟩ :=
    hcomp k G H hG.isSemisimple j hj hs hc hn
  let m := commutingSubgroupMultiplicationHom j i hcomm
  have : IsIso m := hG.central_isogeny_isIso (H ⊗ K) m hprod hm
  exact (hG.of_iso (asIso m)).of_tensor_left hH hK

/-- Under the explicit normal-complement premise, a semisimple central cover
of a smooth connected closed normal subgroup is an actual isomorphism. -/
def IsSimplyConnected.normalFactorCoverIso_of_normalIsogenyComplement
    (hG : IsSimplyConnected G)
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (hn : (SubgroupFunctor.range j).IsNormal)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (f : C ⟶ H) (hC : IsSemisimple C) (hf : IsCentralIsogeny f) : C ≅ H := by
  letI : IsIso f :=
    (hG.normalSubgroup_of_normalIsogenyComplement hcomp j hj hs hc hn).central_isogeny_isIso
      C f hC hf
  exact asIso f

/-- The constructed normal-factor cover isomorphism has the original map. -/
@[simp]
theorem IsSimplyConnected.normalFactorCoverIso_of_normalIsogenyComplement_hom
    (hG : IsSimplyConnected G)
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (hn : (SubgroupFunctor.range j).IsNormal)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (f : C ⟶ H) (hC : IsSemisimple C) (hf : IsCentralIsogeny f) :
    (hG.normalFactorCoverIso_of_normalIsogenyComplement hcomp j hj hs hc hn f hC hf).hom =
      f := rfl

end Langlands.GroupScheme
