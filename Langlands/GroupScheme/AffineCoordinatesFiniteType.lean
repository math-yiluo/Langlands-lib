import Langlands.GroupScheme.AffineCorepresented
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite type of affine group coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

set_option linter.defProp false in
/-- The chosen affine coordinate algebra is finite type when the structure morphism is
locally of finite type. -/
@[instance_reducible]
def algebraFiniteType [LocallyOfFiniteType G.X.hom] :
    Algebra.FiniteType R (algebra G) := by
  let f := (coordinateCogroupIso G).hom.hom.hom
  have : IsIso f.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso (coordinateCogroupIso G))).hom)
  have h : LocallyOfFiniteType (f.left ≫ G.X.hom) := inferInstance
  simp only [Over.w] at h
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap R (algebra G)))) at h
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

attribute [instance] algebraFiniteType

end Langlands.GroupScheme.AffineCoordinates
