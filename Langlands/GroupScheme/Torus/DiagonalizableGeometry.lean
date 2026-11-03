import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.FiniteType

/-! # Finite-type geometry of diagonalizable group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- The actual diagonalizable group scheme is affine over its given base. -/
instance isAffineHom : IsAffineHom (groupScheme R Λ).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom
    (algebraMap R (AddMonoidAlgebra R Λ))))
  infer_instance

/-- Finite generation of the full character group gives finite type, including
when that character group has torsion. -/
instance locallyOfFiniteType [AddGroup.FG Λ] :
    LocallyOfFiniteType (groupScheme R Λ).X.hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap R (AddMonoidAlgebra R Λ))))
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  change (algebraMap R (AddMonoidAlgebra R Λ)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

end Langlands.GroupScheme.Diagonalizable
