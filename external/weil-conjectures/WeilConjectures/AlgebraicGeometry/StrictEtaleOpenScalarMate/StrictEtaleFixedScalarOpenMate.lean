/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! Scalar compatibility of fixed-coefficient open extension by zero.

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ.
(blueprint: lem-pur-fixed-scalar-open-inverse-mate). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.StrictEtaleOpenScalarMate

/-- The inverse mate of the scalar restriction square is invertible.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ.
(blueprint: lem-pur-fixed-scalar-open-inverse-mate).

Proof: restriction of scalars is left adjoint to scalar coextension. Coextension
preserves sheaves and commutes literally with restriction to the open subsite.
Taking its inverse mate gives the identity scalar-restriction square, by the
triangle identity on each section. Taking the inverse mate a second time is
conjugation by the composite adjunctions, so preserves this isomorphism. -/
theorem fixed_scalar_mate_iso
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (f : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso ((mateEquiv
      (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
      (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
        (.mk (Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j)
          (Sheaf.restrictScalars Z.smallEtaleTopology f)
          (Sheaf.restrictScalars X.smallEtaleTopology f)
          (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j) (𝟙 _))) := by
  let a := Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j
  let b := Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  let am : ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f ⊣
      ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} f :=
    ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f
  let := am.isRightAdjoint
  let c := sheafComposeAdjunction X.smallEtaleTopology am
  let d := sheafComposeAdjunction Z.smallEtaleTopology am
  let γ : TwoSquare
      (sheafCompose Z.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} f))
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j)
      (sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} f)) :=
    .mk _ _ _ _ (𝟙 _)
  have hγ : ((mateEquiv d c).symm γ) = 𝟙 _ := by
    ext M U x
    simp only [comp_obj, mateEquiv_symm_apply, NatTrans.comp_app, id_obj,
      leftUnitor_inv_app, whiskerRight_app, Functor.comp_map, associator_inv_app,
      associator_hom_app, map_id, whiskerLeft_app, rightUnitor_hom_app,
      Category.comp_id, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
      sheafCompose_map_hom, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_id]
    change (am.counit.app _).hom
      (((ModuleCat.restrictScalars f).map (am.unit.app _)).hom x) = x
    exact ConcreteCategory.congr_hom (am.left_triangle_components _) x
  have he := iterated_mateEquiv_conjugateEquiv_symm a b c d γ
  have hβ : (mateEquiv d c).symm γ =
      .mk (Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j)
        (Sheaf.restrictScalars Z.smallEtaleTopology f)
        (Sheaf.restrictScalars X.smallEtaleTopology f)
        (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j) (𝟙 _) := by
    exact hγ
  rw [hβ] at he
  rw [he]
  change IsIso ((conjugateEquiv (a.comp d) (c.comp b)).symm γ)
  have : IsIso γ := by dsimp [γ]; infer_instance
  exact conjugateEquiv_symm_iso (a.comp d) (c.comp b) γ

end AlgebraicGeometry.StrictEtaleOpenScalarMate
