import Langlands.AlgebraicGeometry.Modules.RelativeFlatness

/-! # The linear unit-stalk comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

private def unitStalkAddIso (X : Scheme.{u}) (x : X) :
    TopCat.Presheaf.stalk (SheafOfModules.unit X.ringCatSheaf).val.presheaf x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).obj (X.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

private lemma unitStalkAddIso_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) :
    (unitStalkAddIso X x).hom
      (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf U x hx r) =
        X.presheaf.germ U x hx r := by
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) r

/-- The actual stalk of the unit module sheaf is the local ring, linearly
over the canonical local-ring action. -/
def unitStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    stalk (SheafOfModules.unit X.ringCatSheaf) x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  __ := (unitStalkAddIso X x).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (SheafOfModules.unit X.ringCatSheaf).val.presheaf m hxU
    change Γ(X, V) at m
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
    erw [← PresheafOfModules.germ_smul
      (SheafOfModules.unit X.ringCatSheaf).val x V hxV]
    change (unitStalkAddIso X x).hom
        (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf V x hxV
          (@Mul.mul Γ(X, V) _ (X.presheaf.map (homOfLE hVU).op r) m)) =
      @Mul.mul (X.presheaf.stalk x) _
        (X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r))
        ((unitStalkAddIso X x).hom
          (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf V x hxV m))
    rw [unitStalkAddIso_germ, unitStalkAddIso_germ]
    exact (X.presheaf.germ V x hxV).hom.map_mul _ _

@[simp]
lemma unitStalkLinearEquiv_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) :
    unitStalkLinearEquiv X x
      (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf U x hx r) =
        X.presheaf.germ U x hx r :=
  unitStalkAddIso_germ X x U hx r

end Langlands.AlgebraicGeometry.Modules
