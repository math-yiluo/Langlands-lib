import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Pullback and isomorphism transport of fibrewise maximal tori -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Transport

variable {S S' : Scheme.{u}} {T T' : CommGroupScheme S}
  {G G' : GroupScheme S} {i : T.toGrp ⟶ G}

end Transport

namespace splitTorus

variable {S S' : Scheme.{u}} (I : Type u) [Finite I]
  (G : GroupScheme S) (i : splitTorus S I ⟶ G) (b : S' ⟶ S)

/-- A pulled-back closed coordinate torus remains closed when expressed in
 the canonical coordinates of the new base. -/
theorem isClosedSubgroup_coordinateBaseChange
    (hi : IsClosedSubgroup i) :
    IsClosedSubgroup ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) :=
  IsClosedSubgroup.iso_comp (baseChangeIso b I).symm (hi.baseChange b)

/-- A pulled-back fibrewise maximal coordinate torus remains fibrewise
 maximal when expressed in the canonical coordinates of the new base. -/
theorem isFibrewiseMaximalTorus_coordinateBaseChange
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme S I) i) :
    IsFibrewiseMaximalTorus (T := commGroupScheme S' I)
      ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) := by
  intro s
  exact isMaximalTorus_baseChangedHom_comp I G i b (S'.fromSpecResidueField s)
    (hi.fieldPoint (S'.fromSpecResidueField s ≫ b))

/-- Pull back a closed fibrewise maximal coordinate torus, retaining the
 actual map and both certified properties. -/
def fibrewiseMaximalBaseChange
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hic : IsClosedSubgroup i)
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme S I) i) :
    {j : splitTorus S' I ⟶ (GroupScheme.baseChange b).obj G //
      IsClosedSubgroup j ∧ IsFibrewiseMaximalTorus (T := commGroupScheme S' I) j} :=
  ⟨(baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i,
    isClosedSubgroup_coordinateBaseChange I G i b hic,
    isFibrewiseMaximalTorus_coordinateBaseChange I G i b hi⟩

end splitTorus

end Langlands.GroupScheme
