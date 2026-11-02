import Langlands.GroupScheme.Rational.PointTopology
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Subgroup

/-! # Actual scheme-center points and central point quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [CommRing F]

/-- The full all-test scheme-center functor evaluated at the identity test `Spec F`. -/
def schemeCenterPoints (M : GroupScheme (Spec (CommRingCat.of F))) :
    Subgroup (rationalPoints M) :=
  (center M).carrier (Over.mk (𝟙 _))

theorem schemeCenterPoints_le_center (M : GroupScheme (Spec (CommRingCat.of F))) :
    schemeCenterPoints M ≤ Subgroup.center (rationalPoints M) :=
  center_carrier_le_center M

instance schemeCenterPoints_isMulCommutative
    (M : GroupScheme (Spec (CommRingCat.of F))) : IsMulCommutative (schemeCenterPoints M) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_center x.property y.val).eq⟩⟩

/-- The canonical inclusion of scheme-center points into the abstract rational-point center. -/
def schemeCenterPointsToCenter (M : GroupScheme (Spec (CommRingCat.of F))) :
    schemeCenterPoints M →* Subgroup.center (rationalPoints M) :=
  Subgroup.inclusion (schemeCenterPoints_le_center M)

@[simp] theorem schemeCenterPointsToCenter_val
    (M : GroupScheme (Spec (CommRingCat.of F))) (z : schemeCenterPoints M) :
    (schemeCenterPointsToCenter M z).val = z.val := rfl

variable {H M : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual rational-point map of a central homomorphism, with its codomain restricted
to the full scheme-center points. -/
def centralRationalPointsMap (i : H ⟶ M) (hi : IsCentral i) :
    rationalPoints H →* schemeCenterPoints M where
  toFun a := ⟨rationalPoints.map i a, hi _ a⟩
  map_one' := Subtype.ext (map_one (rationalPoints.map i))
  map_mul' a b := Subtype.ext (map_mul (rationalPoints.map i) a b)

@[simp] theorem centralRationalPointsMap_val (i : H ⟶ M) (hi : IsCentral i)
    (a : rationalPoints H) :
    (centralRationalPointsMap i hi a).val = rationalPoints.map i a := rfl

/-- The image of the actual central point map, as a subgroup of scheme-center points. -/
def centralRationalPointImage (i : H ⟶ M) (hi : IsCentral i) :
    Subgroup (schemeCenterPoints M) :=
  (centralRationalPointsMap i hi).range

theorem mem_centralRationalPointImage (i : H ⟶ M) (hi : IsCentral i)
    (z : schemeCenterPoints M) :
    z ∈ centralRationalPointImage i hi ↔
      ∃ a : rationalPoints H, rationalPoints.map i a = z.val := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- This is the same actual image subgroup, expressed by restriction from the ambient group. -/
theorem centralRationalPointImage_eq_subgroupOf (i : H ⟶ M) (hi : IsCentral i) :
    centralRationalPointImage i hi =
      (rationalPoints.map i).range.subgroupOf (schemeCenterPoints M) := by
  ext z
  exact mem_centralRationalPointImage i hi z

instance centralRationalPointImage_normal (i : H ⟶ M) (hi : IsCentral i) :
    (centralRationalPointImage i hi).Normal := inferInstance

/-- The quotient of full scheme-center rational points by the actual image on rational points.
No scheme quotient is used. -/
abbrev CentralPointQuotient (i : H ⟶ M) (hi : IsCentral i) :=
  schemeCenterPoints M ⧸ centralRationalPointImage i hi

section Topology

variable [TopologicalSpace F] (M) [IsAffine M.X.left]

/-- The subgroup topology inherited from the canonical topology on `M(F)`. -/
@[instance_reducible]
def schemeCenterPointTopology : TopologicalSpace (schemeCenterPoints M) := by
  letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  exact inferInstance

variable {M}

/-- The quotient topology of the canonical inherited topology on the full scheme-center points.
This is explicit data, rather than a global topology instance. -/
@[instance_reducible]
def centralPointQuotientTopology (i : H ⟶ M) (hi : IsCentral i) :
    TopologicalSpace (CentralPointQuotient i hi) := by
  letI : TopologicalSpace (schemeCenterPoints M) := schemeCenterPointTopology M
  exact inferInstance

end Topology

end Langlands.GroupScheme
