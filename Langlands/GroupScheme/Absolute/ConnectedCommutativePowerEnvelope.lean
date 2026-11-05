import Langlands.GroupScheme.Absolute.SmoothRationalPointClosure
import Langlands.GroupScheme.IdentityComponentPowers

/-! # A positive power inside a smooth connected commutative closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual connected commutative closed subgroup containing a positive power
of the specified rational point. -/
structure ConnectedCommutativePowerEnvelope {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : rationalPoints G) where
  group : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : group.toGrp ⟶ G
  point : rationalPoints group.toGrp
  exponent : ℕ
  exponent_pos : 0 < exponent
  closed : IsClosedSubgroup inclusion
  smooth : Smooth group.toGrp.X.hom
  affine : IsAffineHom group.toGrp.X.hom
  connected : ConnectedSpace group.toGrp.X.left
  geometricallyConnected : GeometricallyConnected group.toGrp.X.hom
  point_inclusion : rationalPoints.map inclusion point = x ^ exponent

/-- Take the identity component of the smooth commutative cyclic closure and
lift the positive power determined by its finite component permutation. -/
def connectedCommutativePowerEnvelope {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    ConnectedCommutativePowerEnvelope G x := by
  let E := smoothCommutativePointEnvelope G x
  let : Smooth E.group.toGrp.X.hom := E.smooth
  let : IsAffineHom E.group.toGrp.X.hom := E.affine
  let C := identityComponent E.group.toGrp
  let j : C ⟶ E.group.toGrp := identityComponentι E.group.toGrp
  have hcomm : IsCommMonObj C.X := by
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro T
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (cancel_mono j.hom.hom).1
    simp only [MonObj.mul_comp]
    exact mul_comm _ _
  let H : CommGroupScheme (Spec (CommRingCat.of k)) := { toGrp := C, comm := hcomm }
  let i : H.toGrp ⟶ G := j ≫ E.inclusion
  have hi : IsClosedSubgroup i := by
    have : IsClosedImmersion E.inclusion.hom.hom.left := E.closed
    change IsClosedImmersion (j.hom.hom.left ≫ E.inclusion.hom.hom.left)
    infer_instance
  refine
    { group := H
      inclusion := i
      point := IdentityComponent.positivePowerPoint E.group.toGrp E.point
      exponent := IdentityComponent.positivePowerExponent E.group.toGrp E.point
      exponent_pos := IdentityComponent.positivePowerExponent_pos E.group.toGrp E.point
      closed := hi
      smooth := inferInstanceAs (Smooth C.X.hom)
      affine := inferInstanceAs (IsAffineHom C.X.hom)
      connected := inferInstanceAs (ConnectedSpace C.X.left)
      geometricallyConnected := inferInstanceAs (GeometricallyConnected C.X.hom)
      point_inclusion := ?_ }
  change IdentityComponent.positivePowerPoint E.group.toGrp E.point ≫
    (j.hom.hom ≫ E.inclusion.hom.hom) = _
  rw [← Category.assoc, IdentityComponent.positivePowerPoint_inclusion]
  change rationalPoints.map E.inclusion
    (E.point ^ IdentityComponent.positivePowerExponent E.group.toGrp E.point) = _
  rw [map_pow, E.point_inclusion]

end Langlands.GroupScheme
