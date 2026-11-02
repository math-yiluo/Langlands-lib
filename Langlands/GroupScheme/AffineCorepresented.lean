import Langlands.GroupScheme.CorepresentedPoints

/-! # Corepresented coordinates for arbitrary affine group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} (C : Grp (CommAlgCat R)ᵒᵖ)

/-- The algebra-valued points of an algebra cogroup, as a group-valued functor. -/
def cogroupFunctor : CommAlgCat R ⥤ GrpCat.{u} :=
  opOp _ ⋙ yonedaGrp.obj C

/-- Algebra homomorphisms corepresent the points of an algebra cogroup. -/
def cogroupCorepresentation :
    (cogroupFunctor C ⋙ forget GrpCat).CorepresentableBy C.X.unop where
  homEquiv :=
    { toFun := fun f => f.op
      invFun := fun f => f.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  homEquiv_comp _ _ := rfl

/-- Reconstructing an algebra cogroup from its point functor recovers the group object. -/
def cogroupRecoveryIso :
    cogroup (cogroupFunctor C) (cogroupCorepresentation C) ≅ C :=
  yonedaGrpFullyFaithful.preimageIso
    (pointsIso (cogroupFunctor C) (cogroupCorepresentation C))

end Corepresented

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- Every affine group scheme lies in the essential image of relative spectrum
on algebra cogroups. -/
theorem mem_essImage : (algSpec R).mapGrp.essImage G := by
  rw [Functor.essImage_mapGrp, essImage_algSpec]
  infer_instance

/-- A chosen algebra cogroup whose relative spectrum is the given affine group. -/
def coordinateCogroup : Grp (CommAlgCat R)ᵒᵖ :=
  (mem_essImage G).witness

/-- The essential-image comparison is an isomorphism of group schemes. -/
def coordinateCogroupIso : (algSpec R).mapGrp.obj (coordinateCogroup G) ≅ G :=
  (mem_essImage G).getIso

/-- A coordinate algebra for an arbitrary affine group scheme. -/
abbrev algebra : CommAlgCat R := (coordinateCogroup G).X.unop

/-- The group-valued algebra-point functor used by the coordinate construction. -/
abbrev functor : CommAlgCat R ⥤ GrpCat.{u} :=
  Corepresented.cogroupFunctor (coordinateCogroup G)

/-- The coordinate algebra corepresents the chosen point functor. -/
abbrev corepresentation : (functor G ⋙ forget GrpCat).CorepresentableBy (algebra G) :=
  Corepresented.cogroupCorepresentation (coordinateCogroup G)

/-- The corepresented group scheme is isomorphic to the original affine group,
including its multiplication, identity and inverse. -/
def groupSchemeIso : Corepresented.groupScheme (functor G) (corepresentation G) ≅ G :=
  (algSpec R).mapGrp.mapIso (Corepresented.cogroupRecoveryIso (coordinateCogroup G)) ≪≫
    coordinateCogroupIso G

end AffineCoordinates

end Langlands.GroupScheme
