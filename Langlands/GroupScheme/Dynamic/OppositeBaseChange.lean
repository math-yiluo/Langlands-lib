import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Torus.Lattice

/-! # Base change of the opposite cocharacter

Base change of cocharacters commutes with passing to the opposite cocharacter
`t ↦ χ(t⁻¹)`, and the opposite of the opposite is the original cocharacter.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}

/-- On points, the power map is the power. -/
theorem comp_powerHom {T : Over S} (x : T ⟶ (Gm S).X) (m : ℤ) :
    x ≫ (CommGroupScheme.groupHom (Gm.powerHom S m)).hom.hom = x ^ m := by
  rw [Gm.powerHom_apply, comp_groupHom_zsmul]
  congr 1

/-- Base change commutes with precomposition by the power map `t ↦ tᵐ`. -/
theorem baseChangeCocharacter_powerHom (χ : (Gm S).toGrp ⟶ G) (m : ℤ) :
    baseChangeCocharacter b (CommGroupScheme.groupHom (Gm.powerHom S m) ≫ χ) =
      CommGroupScheme.groupHom (Gm.powerHom S' m) ≫ baseChangeCocharacter b χ := by
  apply hom_ext_points
  intro T t
  apply (baseChangePointsEquiv b G T).injective
  have h1 : (t ^ m) ≫ (Gm.baseChangeIso b).inv.hom.hom =
      (t ≫ (Gm.baseChangeIso b).inv.hom.hom) ^ m := GrpObj.zpow_comp t m _
  rw [baseChangePointsEquiv_baseChangeCocharacter, Grp.comp_hom_hom, ← Category.assoc,
    comp_powerHom, Grp.comp_hom_hom, ← Category.assoc, comp_powerHom,
    baseChangePointsEquiv_baseChangeCocharacter, h1, map_zpow]

/-- The opposite of the opposite cocharacter is the cocharacter. -/
theorem powerHom_neg_one_comp_powerHom_neg_one (χ : (Gm S).toGrp ⟶ G) :
    CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫
        CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ = χ := by
  apply hom_ext_points
  intro T t
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_powerHom, Grp.comp_hom_hom, ← Category.assoc,
    comp_powerHom, ← zpow_mul]
  norm_num

end Dynamic

end Langlands.GroupScheme
