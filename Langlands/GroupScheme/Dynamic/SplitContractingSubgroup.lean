import Langlands.GroupScheme.Dynamic.UnipotentTorusAction
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Rational.TorusUnipotenceProof
import Langlands.GroupScheme.Rational.TorusSplitUnipotenceProof

/-! # Actual split-unipotent contracting subgroups

The existing torus-action unipotence and splitness proofs apply to every
representative of a dynamic contracting subgroup. For an arbitrary Gm-action,
the semidirect-product construction supplies an actual closed representative
with its smoothness, connectedness and split-unipotence proofs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {j : H ⟶ G}

/-- Every closed representative of a dynamic contracting subgroup is
unipotent, without any additional structural premise. -/
theorem isUnipotent_of_isRepresentedBy_unipotent
    (hj : (unipotent χ).IsRepresentedBy j) (hc : IsClosedSubgroup j) :
    IsUnipotent H :=
  isUnipotent_of_torusActionUnipotence χ
    RelativeRoot.torusActionUnipotence hj hc

/-- Every closed representative of a dynamic contracting subgroup is split
unipotent in the existing finite Ga-series sense. -/
theorem isSplitUnipotent_of_isRepresentedBy_unipotent
    (hj : (unipotent χ).IsRepresentedBy j) (hc : IsClosedSubgroup j) :
    RelativeRoot.IsSplitUnipotent H := by
  let : IsAffineHom H.X.hom := hc.isAffineHom
  exact RelativeRoot.torusActionSplitUnipotence k H
    ((dynamicSmooth k G χ H j).2.2 hj) inferInstance
    (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hj)
    (isUnipotent_of_isRepresentedBy_unipotent χ hj hc)
    (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm
    (unipotentConjugationAction χ j hj)
    (actionWeightSpace_unipotentConjugationAction_zero χ j hj)

end Dynamic

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual group-scheme data for the full identity-limit subgroup of the
supplied action; no choice of rational-point subgroup is involved. -/
structure SplitContractingSubgroup
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  isRepresentedBy : a.unipotent.IsRepresentedBy inclusion
  isClosedSubgroup : IsClosedSubgroup inclusion
  smooth : Smooth group.X.hom
  connectedSpace : ConnectedSpace group.X.left
  isUnipotent : IsUnipotent group
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent group

variable [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

/-- The existing actual semidirect-product representative carries all the
split-unipotent contracting-subgroup structure. -/
def splitContractingSubgroup : SplitContractingSubgroup a := by
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
    isSplitTorus_gm.isAffineHom
  let : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _
  let : IsAffine a.semidirectProduct.X.left :=
    isAffine_of_isAffineHom a.semidirectProduct.X.hom
  let hj := Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr
  let hc := Dynamic.Affine.isClosedSubgroup_unipotentHom a.semidirectInr
  exact
    { group := Affine.unipotentScheme a
      inclusion := Affine.unipotentHom a
      isRepresentedBy := Affine.isRepresentedBy_unipotentHom a
      isClosedSubgroup := Affine.isClosedSubgroup_unipotentHom a
      smooth := Affine.smooth_unipotentScheme a
      connectedSpace :=
        DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent
          a.semidirectProduct a.semidirectInr hj
      isUnipotent :=
        Dynamic.isUnipotent_of_isRepresentedBy_unipotent a.semidirectInr hj hc
      isSplitUnipotent :=
        Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent a.semidirectInr hj hc }

/-- The package records the full identity-limit functor on every test. -/
theorem splitContractingSubgroup_range :
    SubgroupFunctor.range (a.splitContractingSubgroup.inclusion) = a.unipotent :=
  a.splitContractingSubgroup.isRepresentedBy.2

end AutomorphicAction

end Langlands.GroupScheme
