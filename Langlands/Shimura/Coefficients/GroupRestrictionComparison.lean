import Langlands.Shimura.Coefficients.VaryingSystemGroupCoverChange

/-! # Identity coefficient comparisons for successive group restriction -/

universe uG uI vI uC vC

open CategoryTheory

set_option autoImplicit false

namespace Langlands.EquivariantDiagram

variable {I : Type uI} [Category.{vI} I]
  {D E F : I ⥤ GrpCat.{uG}}
  {C : Type uC} [Category.{vC} C]
  (φ : D ⟶ E) (ψ : E ⟶ F) (χ : D ⟶ F)
  (h : ∀ i, (ψ.app i).hom.comp (φ.app i).hom = (χ.app i).hom)

/-- Equality of the actual composite group maps identifies the two restrictions
by the identity on the complete underlying coefficient diagram. -/
def groupRestrictionCompIso (M : EquivariantDiagram F C) :
    (groupRestriction C φ).obj ((groupRestriction C ψ).obj M) ≅
      (groupRestriction C χ).obj M where
  hom :=
    { hom := 𝟙 M.obj
      comm i g := by
        change M.ρ i ((ψ.app i).hom ((φ.app i).hom g)) ≫ 𝟙 _ =
          𝟙 _ ≫ M.ρ i ((χ.app i).hom g)
        simp only [Category.comp_id, Category.id_comp]
        exact congrArg (M.ρ i) (congrArg (fun f => f g) (h i)) }
  inv :=
    { hom := 𝟙 M.obj
      comm i g := by
        change M.ρ i ((χ.app i).hom g) ≫ 𝟙 _ =
          𝟙 _ ≫ M.ρ i ((ψ.app i).hom ((φ.app i).hom g))
        simp only [Category.comp_id, Category.id_comp]
        exact congrArg (M.ρ i) (congrArg (fun f => f g) (h i)).symm }
  hom_inv_id := by apply Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Hom.ext; exact Category.id_comp _

@[simp] theorem groupRestrictionCompIso_hom_hom (M : EquivariantDiagram F C) :
    (groupRestrictionCompIso φ ψ χ h M).hom.hom = 𝟙 M.obj := rfl

@[simp] theorem groupRestrictionCompIso_inv_hom (M : EquivariantDiagram F C) :
    (groupRestrictionCompIso φ ψ χ h M).inv.hom = 𝟙 M.obj := rfl

/-- These identities commute with every original equivariant coefficient map. -/
@[reassoc] theorem groupRestrictionCompIso_naturality
    {M N : EquivariantDiagram F C} (c : M ⟶ N) :
    (groupRestriction C φ).map ((groupRestriction C ψ).map c) ≫
        (groupRestrictionCompIso φ ψ χ h N).hom =
      (groupRestrictionCompIso φ ψ χ h M).hom ≫
        (groupRestriction C χ).map c := by
  apply Hom.ext
  exact (Category.comp_id c.hom).trans (Category.id_comp c.hom).symm

end Langlands.EquivariantDiagram
