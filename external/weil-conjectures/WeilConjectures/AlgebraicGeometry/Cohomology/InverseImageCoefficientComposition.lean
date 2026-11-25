/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
/-! # Composition of inverse images and coefficient units

Source: Stacks Project, Section 01F7, functoriality of pullback.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {X Y Z : Scheme.{u}}

/-- The coefficient morphism induced by the module pullback unit.
Source: Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def coefficientUnit (f : Y ⟶ X) (M : X.Modules) :=
  coeff f ((pullbackPushforwardAdjunction f).unit.app M)

/-- The inverse-image composition comparison, determined by the adjunctions.
Source: Mathlib `Adjunction.leftAdjointCompIso`; Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def invImageComp (g : Z ⟶ Y) (f : Y ⟶ X) :
    invImage f ⋙ invImage g ≅ invImage (g ≫ f) :=
  Adjunction.leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (g ≫ f).base)
    (Iso.refl _)

/-- Inverse images along equal morphisms identify.
Source: equality transport; Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def invImageCongr {f g : Y ⟶ X} (h : f = g) :
    invImage f ≅ invImage g := eqToIso (congrArg invImage h)

/-- Coefficient units compose under the canonical comparisons.
Source: Stacks Project, Section 01F7, functoriality of pullback.
(blueprint: lem-pc-coefficient-unit-composition)

Proof: Postcompose both sides with the forgotten inverse of pullbackComp g f.
This is an isomorphism, so it suffices to prove the resulting equality. Apply
the composite abelian inverse-image/direct-image adjunction to both morphisms.
The adjunct of the left hand side is the composite of the two module units,
after forgetting to abelian sheaves. The adjunct of the right hand side is
the unit for the composite followed by the inverse of the module pullback
composition comparison. These agree by pullbackUnit_comp_app on every open.
The abelian composition comparison is the unique left-adjoint comparison,
so its adjunct is precisely the composite abelian unit. Injectivity of the
adjunction hom equivalence proves the equality. This works for all morphisms,
including identities, empty schemes and zero modules.
-/
@[reassoc]
theorem coefficientUnit_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) :
    (invImage g).map (coefficientUnit f M) ≫
        coefficientUnit g ((pullback f).obj M) ≫
        (SheafOfModules.toSheaf Z.ringCatSheaf).map ((pullbackComp g f).hom.app M) =
      (invImageComp g f).hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≫
        coefficientUnit (g ≫ f) M := by
  let af := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let ag := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
  let ac := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (g ≫ f).base
  apply (cancel_mono ((SheafOfModules.toSheaf Z.ringCatSheaf).map
    ((pullbackComp g f).inv.app M))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [(SheafOfModules.toSheaf Z.ringCatSheaf).map_id, Category.comp_id]
  have hc := unit_conjugateEquiv_symm ac (af.comp ag) (𝟙 _)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
  change ac.unit.app _ ≫ 𝟙 _ =
    (af.comp ag).unit.app _ ≫ _ at hc
  erw [Category.comp_id] at hc
  apply ((af.comp ag).homEquiv _ _).injective
  have hl : (af.comp ag).homEquiv _ _
      ((invImage g).map (coefficientUnit f M) ≫ coefficientUnit g _) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map (pullbackUnit f M) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map (pullbackUnit g _)) := by
    erw [Adjunction.comp_homEquiv]
    change af.homEquiv _ _ (ag.homEquiv _ _
      ((invImage g).map (coefficientUnit f M) ≫ coefficientUnit g _)) = _
    erw [ag.homEquiv_naturality_left]
    simp only [coefficientUnit, coeff, af, ag]
    erw [af.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  erw [hl]
  conv_rhs =>
    erw [(af.comp ag).homEquiv_naturality_right]
    erw [Adjunction.homEquiv_unit]
  erw [← hc]
  erw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← ac.homEquiv_unit]
  simp only [coefficientUnit, coeff, ac]
  erw [Equiv.apply_symm_apply]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (pullbackUnit_comp_app g f M U.unop).symm

end AlgebraicGeometry.Scheme.Modules
