/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartRestriction

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open Scheme.Modules
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A commuting affine sheaf square gives the required equality of chart sections. -/
theorem tensorResolutionSection_naturality (Y : Scheme.{u}) (Q : Y.Modules)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (HA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (HB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (dA : tilde HA ≅ Q.restrict U.2.fromSpec)
    (dB : tilde HB ≅ Q.restrict V.2.fromSpec)
    (a : HA ⟶ (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).obj HB)
    (hd : (restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map dA.hom ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app Q =
      tensorResolutionSemilinearMap (Y.presheaf.map (homOfLE h).op) a ≫ dB.hom)
    (x : HA) :
    Q.val.map (homOfLE h).op
        (sectionsRestrictFromSpecLinearEquiv Q U.2 (dA.hom.app ⊤ (tilde.toOpen HA ⊤ x))) =
      sectionsRestrictFromSpecLinearEquiv Q V.2
        (dB.hom.app ⊤ (tilde.toOpen HB ⊤ (a x))) := by
  let φ := Y.presheaf.map (homOfLE h).op
  rw [← tensorResolutionChartRestriction_sections Y Q V U h]
  have hu := congrArg (fun f ↦ f.app ⊤ (tilde.toOpen HA ⊤ x))
    ((restrictAdjunction (Spec.map φ)).unit.naturality dA.hom)
  change ((restrictAdjunction (Spec.map φ)).unit.app (Q.restrict U.2.fromSpec)).app ⊤
      (dA.hom.app ⊤ (tilde.toOpen HA ⊤ x)) =
    (((restrictFunctor (Spec.map φ)).map dA.hom).app ⊤
      (((restrictAdjunction (Spec.map φ)).unit.app (tilde HA)).app ⊤
        (tilde.toOpen HA ⊤ x))) at hu
  rw [hu]
  have hd' := congrArg (fun f ↦ f.app ⊤
    (((restrictAdjunction (Spec.map φ)).unit.app (tilde HA)).app ⊤
      (tilde.toOpen HA ⊤ x))) hd
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hd'
  exact congrArg (sectionsRestrictFromSpecLinearEquiv Q V.2)
    (hd'.trans (congrArg (dB.hom.app ⊤) (tensorResolutionSemilinearMap_unit φ a x)))

end AlgebraicGeometry
