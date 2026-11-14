import Langlands.GroupScheme.Torus.WeylGroupSchemeFibreCardinality
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Constant point Weyl order for a split maximal torus over a local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The Weyl order of a coordinate torus map on the closed residue field
of a local base ring. -/
def localSplitWeylOrder
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) : ℕ :=
  Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
    (splitTorus.baseChangeHom (K := IsLocalRing.ResidueField R) G I i))

/-- A common full coordinate root datum gives the actual Weyl order on
every supplied field-valued fibre. -/
theorem IsFibrewiseRootDatumOf.natCard_relativeWeylGroup
    {R : Type u} [CommRing R] (I : Type u) [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (k : Type u) [Field k] [Algebra R k] :
    Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := k) G I i)) = Nat.card P.weylGroup := by
  let := hG.smooth
  have hred := hG.isConnectedReductive_baseChange (algebraBaseMap R k)
  have htorus : IsSplitTorus (splitTorus (Spec (CommRingCat.of k)) I) :=
    isSplitTorus_splitTorus I
  have hmaxk := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k
  have hPk := hP.field k
  have hcard := natCard_relativeWeylGroup_eq_rootDatum
    (G := (baseChange (algebraBaseMap R k)).obj G)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    hred htorus (splitTorus.baseChangeHom (K := k) G I i) hmaxk
    (CoordinateRootDatum.fieldRealization k P) hPk
  exact hcard.trans (CoordinateRootDatum.natCard_weylGroup_fieldRealization k P)

/-- The point Weyl order on every supplied field-valued fibre equals the
order on the closed residue field. -/
theorem natCard_relativeWeylGroup_eq_localSplitWeylOrder
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (k : Type u) [Field k] [Algebra R k] :
    Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := k) G I i)) = localSplitWeylOrder I G i := by
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistence R G hG I i hi hmax
  exact (hP.natCard_relativeWeylGroup I hG i hmax k).trans
    (hP.natCard_relativeWeylGroup I hG i hmax (IsLocalRing.ResidueField R)).symm

/-- The actual point Weyl quotient of a closed split torus in an affine
algebraic group has positive finite order. -/
theorem IsSplitTorus.natCard_relativeWeylGroup_pos
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    0 < Nat.card (relativeWeylGroup i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi
  unfold relativeWeylGroup
  rw [← hT.weylAction_ker i]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (weylAction i)).toEquiv]
  change 0 < Nat.card (weylImage i)
  exact Nat.card_pos

/-- A fibrewise maximal coordinate torus in a reductive group over a local
ring has positive common Weyl order. -/
theorem localSplitWeylOrder_pos
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    0 < localSplitWeylOrder I G i := by
  let := hG.smooth
  have hred := hG.isConnectedReductive_baseChange
    (algebraBaseMap R (IsLocalRing.ResidueField R))
  let := hred.smooth
  let := hred.isAffineHom
  have htorus : IsSplitTorus
      (splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) I) :=
    isSplitTorus_splitTorus I
  exact htorus.natCard_relativeWeylGroup_pos
    (G := (baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).obj G)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) I)
    (splitTorus.baseChangeHom (K := IsLocalRing.ResidueField R) G I i)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax _).2.1

end Langlands.GroupScheme
