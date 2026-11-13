import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.RingSmoothConnectedProof
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Rational.RootProductTransport

/-! # Smooth connected root representatives from a ring-level kernel centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction.Affine

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of R))).toGrp G)

/-- The actual identity-limit representative of a smooth affine ring group is smooth. -/
theorem smooth_unipotentScheme_ring : Smooth (unipotentScheme a).X.hom := by
  let : IsAffineHom (Gm (Spec (CommRingCat.of R))).X.hom :=
    isSplitTorus_gm.isAffineHom
  let : Smooth (Gm (Spec (CommRingCat.of R))).X.hom := smooth_gm _
  let : IsAffine a.semidirectProduct.X.left :=
    isAffine_of_isAffineHom a.semidirectProduct.X.hom
  exact ((dynamicRingSmoothConnected R a.semidirectProduct a.semidirectInr
    (unipotentScheme a) (Dynamic.Affine.unipotentHom a.semidirectInr)).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)).1

/-- The same ring-level representative has geometrically connected fibres. -/
theorem geometricallyConnected_unipotentScheme_ring :
    GeometricallyConnected (unipotentScheme a).X.hom := by
  let : IsAffineHom (Gm (Spec (CommRingCat.of R))).X.hom :=
    isSplitTorus_gm.isAffineHom
  let : Smooth (Gm (Spec (CommRingCat.of R))).X.hom := smooth_gm _
  let : IsAffine a.semidirectProduct.X.left :=
    isAffine_of_isAffineHom a.semidirectProduct.X.hom
  exact ((dynamicRingSmoothConnected R a.semidirectProduct a.semidirectInr
    (unipotentScheme a) (Dynamic.Affine.unipotentHom a.semidirectInr)).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom a.semidirectInr)).2

end AutomorphicAction.Affine

namespace RelativeRoot.Ring

variable {R : Type u} [CommRing R]
    {S : CommGroupScheme (Spec (CommRingCat.of R))}
    {G C : GroupScheme (Spec (CommRingCat.of R))}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    [IsAffineHom C.X.hom]
    [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- The actual identity-limit scheme for the descended action on the supplied
kernel centralizer, over the original ring. -/
def subgroupScheme : GroupScheme (Spec (CommRingCat.of R)) :=
  AutomorphicAction.Affine.unipotentScheme (quotientAction i a j hj)

/-- The root representative's actual map to the ambient group. -/
def subgroupHom : subgroupScheme i a j hj ⟶ G :=
  AutomorphicAction.Affine.unipotentHom (quotientAction i a j hj) ≫ j

/-- The construction represents the full root functor on every base test scheme. -/
theorem isRepresentedBy_subgroupHom (hjc : IsClosedSubgroup j) :
    (subgroup i a).IsRepresentedBy (subgroupHom i a j hj) := by
  rw [quotientActionComparison _ _ _ _ i a j hj hjc]
  exact (AutomorphicAction.Affine.isRepresentedBy_unipotentHom
    (quotientAction i a j hj)).comp hj

/-- A closed supplied kernel centralizer gives a closed root inclusion. -/
theorem isClosedSubgroup_subgroupHom (hjc : IsClosedSubgroup j) :
    IsClosedSubgroup (subgroupHom i a j hj) :=
  (AutomorphicAction.Affine.isClosedSubgroup_unipotentHom
    (quotientAction i a j hj)).comp hjc

/-- The constructed root representative is affine over the ring. -/
instance subgroupScheme_isAffineHom : IsAffineHom (subgroupScheme i a j hj).X.hom :=
  AutomorphicAction.Affine.unipotentScheme_isAffineHom (quotientAction i a j hj)

variable [Smooth C.X.hom]

/-- Smoothness follows from the actual descended action on the smooth centralizer. -/
theorem smooth_subgroupScheme : Smooth (subgroupScheme i a j hj).X.hom :=
  AutomorphicAction.Affine.smooth_unipotentScheme_ring (quotientAction i a j hj)

/-- Geometric connectedness does not require connectedness of the centralizer. -/
theorem geometricallyConnected_subgroupScheme :
    GeometricallyConnected (subgroupScheme i a j hj).X.hom :=
  AutomorphicAction.Affine.geometricallyConnected_unipotentScheme_ring
    (quotientAction i a j hj)

end RelativeRoot.Ring

end Langlands.GroupScheme
