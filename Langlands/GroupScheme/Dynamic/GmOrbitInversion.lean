import Langlands.GroupScheme.Dynamic.SchemeActionLimit
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Torus.Lattice

/-! # Orbits along the opposite cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GmOrbitInversion

open SchemeAction

variable {S : Scheme.{u}}

/-- The power map `t ↦ t⁻¹` of `𝔾ₘ` is the group inversion. -/
theorem groupHom_powerHom_neg_one :
    (CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom = ι[(Gm S).X] := by
  rw [GrpObj.inv_eq_inv, ← Category.id_comp (CommGroupScheme.groupHom _).hom.hom,
    Gm.powerHom_apply, Gm.comp_zsmul_id, zpow_neg_one]

variable {T : CommGroupScheme S} {X : Over S}

/-- On points, the opposite cocharacter is the cocharacter applied to the inverse. -/
theorem comp_groupHom_neg {U : Over S} (x : U ⟶ (Gm S).X) (ν : cocharacterLattice T) :
    x ≫ (CommGroupScheme.groupHom (-ν)).hom.hom =
      (x ≫ (CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom) ≫
        (CommGroupScheme.groupHom ν).hom.hom := by
  rw [groupHom_powerHom_neg_one, ← neg_one_zsmul, comp_groupHom_zsmul, zpow_neg_one,
    ← GrpObj.inv_comp]
  rfl

/-- **Orbits along `-ν`.** For an action of a commutative group scheme, the orbit map of a
point along `-ν` is the orbit map along `ν` precomposed with inversion `t ↦ t⁻¹` of `𝔾ₘ`. -/
theorem gmOrbit_neg (b : SchemeAction T.toGrp X) (ν : cocharacterLattice T) {Z : Over S}
    (w : Z ⟶ X) :
    (b.restrict (CommGroupScheme.groupHom (-ν))).gmOrbit w =
      Z ◁ (CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom ≫
        (b.restrict (CommGroupScheme.groupHom ν)).gmOrbit w := by
  simp only [gmOrbit, restrict_act]
  rw [naturality, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, comp_groupHom_neg,
    Category.assoc]

/-- **Orbits along the opposite cocharacter.** For any action and any cocharacter `χ` of the
acting group, the orbit map along `Dynamic.oppositeCocharacter χ` is the orbit map along `χ`
precomposed with inversion `t ↦ t⁻¹` of `𝔾ₘ`. -/
theorem gmOrbit_oppositeCocharacter {H : GroupScheme S} (b : SchemeAction H X)
    (χ : (Gm S).toGrp ⟶ H) {Z : Over S} (w : Z ⟶ X) :
    (b.restrict (Dynamic.oppositeCocharacter χ)).gmOrbit w =
      Z ◁ (CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom ≫
        (b.restrict χ).gmOrbit w := by
  simp only [gmOrbit, restrict_act]
  rw [naturality, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc]
  rfl

end Langlands.GroupScheme.GmOrbitInversion
