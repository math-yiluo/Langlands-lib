import Langlands.GroupScheme.Torus.WeylGroupSchemeFibreOrder
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Universal local-base orders for split Weyl quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- On every test scheme over a changed base, the point Weyl quotient for the
canonical coordinate source is the original point quotient. -/
def splitTorus.pointWeylGroupBaseChangedEquiv
    {S S' : Scheme.{u}} (I : Type u) [Finite I] (G : GroupScheme S)
    (i : splitTorus S I ⟶ G) (b : S' ⟶ S) (U : Over S') :
    pointWeylGroup (T := splitTorus.commGroupScheme S' I)
        ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) U ≃*
      pointWeylGroup (T := splitTorus.commGroupScheme S I) i
        ((Over.map b).obj U) :=
  (pointWeylGroupSourceIsoEquiv
    (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme S I))
    (T' := splitTorus.commGroupScheme S' I)
    (splitTorus.baseChangeIso b I).symm ((baseChange b).map i) U).trans
      (pointWeylGroupBaseChangeEquiv (T := splitTorus.commGroupScheme S I) b i U)

section SuppliedSplitQuotient

variable {S : Scheme.{u}} (I : Type u) [Fintype I] {G N W : GroupScheme S}
  (hG : IsReductive G) (i : splitTorus S I ⟶ G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
  {n : N ⟶ G}
  (hn : (torusNormalizer (T := splitTorus.commGroupScheme S I) i).IsRepresentedBy n)
  (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
  [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]
  (hker : ∀ (U : Over S) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈
      (torusCentralizer (T := splitTorus.commGroupScheme S I) i).carrier U)

include hG hi hmax hn q hq hker

/-- Over every local-ring base map, all algebraically closed field-valued lifts
into the original quotient have the Weyl order of the coordinate local pullback. -/
theorem natCard_quotientFibre_eq_localSplitWeylOrder_of_baseChange
    {R : Type u} [CommRing R] [IsLocalRing R]
    (b : Spec (CommRingCat.of R) ⟶ S)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k] :
    Nat.card {x : Spec (CommRingCat.of k) ⟶ W.X.left //
      x ≫ W.X.hom = algebraBaseMap R k ≫ b} =
        localSplitWeylOrder I ((baseChange b).obj G)
          ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom ((baseChange b).obj G).X.hom := (hG.baseChange b).isAffineHom
  have hi' : IsClosedSubgroup
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) :=
    (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso b I).symm).comp (hi.baseChange b)
  have hmax' := splitTorus.isFibrewiseMaximalTorus_baseChangedHom I G i hmax b
  exact (Nat.card_congr
    ((weylQuotientFibrePointEquiv (algebraBaseMap R k ≫ b)
      (T := splitTorus.commGroupScheme S I) i hn q hq hker).trans
        (splitTorus.pointWeylGroupBaseChangedEquiv I G i b
          (Over.mk (algebraBaseMap R k))).symm.toEquiv)).trans
    (natCard_pointWeylGroup_eq_localSplitWeylOrder I (hG.baseChange b)
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) hi' hmax' k)

/-- A supplied split Weyl quotient satisfies the universal local-base
constant-cardinality condition, with the original field algebra retained. -/
theorem exists_natCard_quotientFibre_constant_on_local_base
    (R : Type u) [CommRing R] [IsLocalRing R] (b : Spec (CommRingCat.of R) ⟶ S) :
    ∃ d : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      Nat.card {x : Spec (CommRingCat.of k) ⟶ W.X.left //
        x ≫ W.X.hom = algebraBaseMap R k ≫ b} = d :=
  ⟨localSplitWeylOrder I ((baseChange b).obj G)
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i),
    fun k => natCard_quotientFibre_eq_localSplitWeylOrder_of_baseChange
      I hG i hi hmax hn q hq hker b k⟩

end SuppliedSplitQuotient

end Langlands.GroupScheme
