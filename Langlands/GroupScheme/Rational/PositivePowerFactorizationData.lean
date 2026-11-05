import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Langlands.GroupScheme.Absolute.ConnectedCommutativePowerEnvelope
import Langlands.GroupScheme.Rational.PositiveCharacteristicTorusPower
import Langlands.GroupScheme.Rational.PositivePowerFactorizationStatement

/-! # Actual commuting factorization data and closed-envelope transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

/-- The actual rational point of the additive group with coordinate one. -/
abbrev coordinateOnePoint (k : Type u) [CommRing k] :
    rationalPoints (groupScheme (CommRingCat.of k) 1) :=
  ((coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
    (Multiplicative.ofAdd (fun _ => 1)))

end VectorGroup

namespace rationalPoints

@[simp]
theorem map_zero_apply {k : Type u} [CommRing k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (x : rationalPoints H) :
    map (0 : H ⟶ G) x = 1 := by
  change x ≫ (0 : H ⟶ G).hom.hom = 1
  rw [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]

end rationalPoints

/-- Concrete factorization data with a positive exponent and commuting factors. -/
structure TorusAdditivePowerFactorizationData {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : rationalPoints G) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  point : rationalPoints torus.toGrp
  additive : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G
  isTorus : IsTorus torus.toGrp
  closed : IsClosedSubgroup inclusion
  factorization : x ^ exponent = rationalPoints.map inclusion point *
    rationalPoints.map additive (VectorGroup.coordinateOnePoint k)
  commute : Commute (rationalPoints.map inclusion point)
    (rationalPoints.map additive (VectorGroup.coordinateOnePoint k))

/-- Transport an exact factorization inside the connected commutative envelope
to the ambient group. Its two factors commute after this transport. -/
def ConnectedCommutativePowerEnvelope.factorizationOfPointFactors
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {x : rationalPoints G} (E : ConnectedCommutativePowerEnvelope G x)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ E.group.toGrp)
    (t : rationalPoints T.toGrp)
    (φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ E.group.toGrp)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hx : E.point = rationalPoints.map i t *
      rationalPoints.map φ (VectorGroup.coordinateOnePoint k)) :
    TorusAdditivePowerFactorizationData G x where
  exponent := E.exponent
  exponent_pos := E.exponent_pos
  torus := T
  inclusion := i ≫ E.inclusion
  point := t
  additive := φ ≫ E.inclusion
  isTorus := hT
  closed := by
    have : IsClosedImmersion i.hom.hom.left := hi
    have : IsClosedImmersion E.inclusion.hom.hom.left := E.closed
    change IsClosedImmersion (i.hom.hom.left ≫ E.inclusion.hom.hom.left)
    infer_instance
  factorization := by
    rw [Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply, Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply,
      ← map_mul, ← hx, E.point_inclusion]
  commute := by
    rw [Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply, Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply]
    exact (show Commute (rationalPoints.map i t)
      (rationalPoints.map φ (VectorGroup.coordinateOnePoint k)) from mul_comm _ _).map
        (rationalPoints.map E.inclusion)

/-- In positive characteristic, compose the connected-envelope inclusion with
the torus inclusion for a further p-power, and take the zero additive map. -/
def positiveCharacteristicFactorizationData {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G)
    (p : ℕ) [Fact p.Prime] [CharP k p] : TorusAdditivePowerFactorizationData G x := by
  let E := connectedCommutativePowerEnvelope G x
  let : Smooth E.group.toGrp.X.hom := E.smooth
  let : IsAffineHom E.group.toGrp.X.hom := E.affine
  let : ConnectedSpace E.group.toGrp.X.left := E.connected
  let D := positiveCharacteristicTorusPower E.group.toGrp E.point p
  refine
    { exponent := E.exponent * p ^ D.powerIndex
      exponent_pos := Nat.mul_pos E.exponent_pos (pow_pos (Fact.out : p.Prime).pos _)
      torus := D.torus
      inclusion := D.inclusion ≫ E.inclusion
      point := D.point
      additive := 0
      isTorus := D.isTorus
      closed := ?_
      factorization := ?_
      commute := ?_ }
  · have : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
    have : IsClosedImmersion E.inclusion.hom.hom.left := E.closed
    change IsClosedImmersion (D.inclusion.hom.hom.left ≫ E.inclusion.hom.hom.left)
    infer_instance
  · rw [rationalPoints.map_zero_apply, mul_one, pow_mul, ← E.point_inclusion,
      ← map_pow, D.point_power, Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply]
  · rw [rationalPoints.map_zero_apply]
    exact Commute.one_right _

end Langlands.GroupScheme
