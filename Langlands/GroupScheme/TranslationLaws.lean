import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Isomorphisms and section formulas for group-scheme translations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme

namespace CommonAffine

variable {S : Scheme.{u}} (G : Grp (Over S))

/-- Left translation is inverted by left translation by the inverse section. -/
def translationIso (s : Over.mk (𝟙 S) ⟶ G.X) : G.X ≅ G.X where
  hom := translation G s
  inv := translation G s⁻¹
  hom_inv_id := by
    rw [points_translation, translation, GrpObj.comp_inv, inv_mul_cancel_left]
  inv_hom_id := by
    rw [points_translation, translation, GrpObj.comp_inv, mul_inv_cancel_left]

lemma section_comp_translation (s z : Over.mk (𝟙 S) ⟶ G.X) :
    z ≫ translation G s = s * z := by
  rw [points_translation]
  have h : Over.mkIdTerminal.from (Over.mk (𝟙 S)) = 𝟙 _ :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h, Category.id_comp]

lemma translation_apply_section [IsCommMonObj G.X]
    (s z : Over.mk (𝟙 S) ⟶ G.X) (c : S) :
    (translation G s).left (z.left c) = (translation G z).left (s.left c) := by
  have h : z ≫ translation G s = s ≫ translation G z := by
    rw [section_comp_translation, section_comp_translation, mul_comm]
  exact congr(($h).left c)

end CommonAffine

end Langlands.GroupScheme
