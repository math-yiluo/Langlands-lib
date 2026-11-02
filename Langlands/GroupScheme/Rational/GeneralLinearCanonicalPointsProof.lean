import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints

/-! # Canonical rational-point comaps for the block subgroups of GL -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)

/-- The published rational-point equivalence has exactly the canonical coefficient map. -/
theorem rationalPointsEquiv_toMonoidHom (N : ℕ) (R : CommRingCat.{u}) :
    (rationalPointsEquiv N R).toMonoidHom =
      (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom).comp
        (pointsEquiv (Fin N) R (Over.mk (𝟙 (Spec R)))).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  exact glRingEquiv_eq_map (n := Fin N) (globalSectionsEquiv R) _

variable {N : ℕ} (B : BlockShape N) (R : CommRingCat.{u})

/-- The block parabolic's rational points are the comap under the canonical matrix map. -/
theorem blockShapeParabolicPoints_eq_comap :
    (blockShapeParabolic B R).carrier (Over.mk (𝟙 (Spec R))) =
      (B.parabolic R).comap
        ((Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom).comp
          (pointsEquiv (Fin N) R (Over.mk (𝟙 (Spec R)))).toMonoidHom) := by
  rw [← parabolic_blockShapeCocharacter, ← rationalPointsEquiv_toMonoidHom]
  ext x
  exact mem_parabolic_blockShapeCocharacter_iff B x

/-- The block Levi's rational points are the comap under the canonical matrix map. -/
theorem blockShapeLeviPoints_eq_comap :
    (blockShapeLevi B R).carrier (Over.mk (𝟙 (Spec R))) =
      (B.leviSubgroup R).comap
        ((Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom).comp
          (pointsEquiv (Fin N) R (Over.mk (𝟙 (Spec R)))).toMonoidHom) := by
  rw [← centralizer_blockShapeCocharacter, ← rationalPointsEquiv_toMonoidHom]
  ext x
  exact mem_centralizer_blockShapeCocharacter_iff B x

/-- The block unipotent's rational points are the comap under the canonical matrix map. -/
theorem blockShapeUnipotentPoints_eq_comap :
    (blockShapeUnipotent B R).carrier (Over.mk (𝟙 (Spec R))) =
      (B.unipotentSubgroup R).comap
        ((Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom).comp
          (pointsEquiv (Fin N) R (Over.mk (𝟙 (Spec R)))).toMonoidHom) := by
  rw [← unipotent_blockShapeCocharacter, ← rationalPointsEquiv_toMonoidHom]
  ext x
  exact mem_unipotent_blockShapeCocharacter_iff B x

end Langlands.GroupScheme.GeneralLinear
