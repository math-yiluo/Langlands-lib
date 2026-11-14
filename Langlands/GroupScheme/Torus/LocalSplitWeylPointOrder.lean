import Langlands.GroupScheme.Torus.LocalSplitWeylOrder
import Langlands.GroupScheme.Torus.WeylPointTransport

/-! # Point Weyl orders on field-valued tests of a split local base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The rational Weyl quotient of the coordinate field fibre is the original
point Weyl quotient evaluated on that field-valued test scheme. -/
def splitTorus.fibreRelativeWeylGroupEquiv
    {R : Type u} [CommRing R] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (k : Type u) [Field k] [Algebra R k] :
    relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := k) G I i) ≃*
      pointWeylGroup (T := splitTorus.commGroupScheme _ I) i
        (Over.mk (algebraBaseMap R k)) := by
  have hbase := hi.baseChange (algebraBaseMap R k)
  let : IsClosedImmersion ((baseChange (algebraBaseMap R k)).map i).hom.hom.left := hbase
  have hsplit : IsClosedSubgroup (splitTorus.baseChangeHom (K := k) G I i) :=
    (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm).comp
      hbase
  let : IsClosedImmersion (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left := hsplit
  exact (relativeWeylGroupPointEquiv (T := splitTorus.commGroupScheme _ I)
    (splitTorus.baseChangeHom (K := k) G I i)).trans
      ((pointWeylGroupSourceIsoEquiv
        (T := (CommGroupScheme.baseChange (algebraBaseMap R k)).obj
          (splitTorus.commGroupScheme _ I))
        (T' := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm
        ((baseChange (algebraBaseMap R k)).map i) (Over.mk (𝟙 _))).trans
          ((relativeWeylGroupPointEquiv
            (T := (CommGroupScheme.baseChange (algebraBaseMap R k)).obj
              (splitTorus.commGroupScheme _ I))
            ((baseChange (algebraBaseMap R k)).map i)).symm.trans
              (Langlands.GroupScheme.fibreRelativeWeylGroupEquiv
                (T := splitTorus.commGroupScheme _ I)
                (algebraBaseMap R k) i)))

/-- The actual point Weyl quotient evaluated on any field-valued test scheme
over a local split base has the common closed-fibre Weyl order. -/
theorem natCard_pointWeylGroup_eq_localSplitWeylOrder
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (k : Type u) [Field k] [Algebra R k] :
    Nat.card (pointWeylGroup (T := splitTorus.commGroupScheme _ I) i
      (Over.mk (algebraBaseMap R k))) = localSplitWeylOrder I G i :=
  (Nat.card_congr (splitTorus.fibreRelativeWeylGroupEquiv I G i hi k).symm.toEquiv).trans
    (natCard_relativeWeylGroup_eq_localSplitWeylOrder I hG i hi hmax k)

end Langlands.GroupScheme
