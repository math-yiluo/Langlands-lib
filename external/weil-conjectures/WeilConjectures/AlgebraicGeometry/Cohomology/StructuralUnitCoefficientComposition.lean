/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Composition of structural unit coefficient maps

Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Coefficient-level compatibility of the pullback unit with structural maps.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial;
Mathlib's pullback-unit adjunction identity.
(blueprint: lem-pbc-structural-unit-coefficient-composition)

Proof: Write e for pullbackObjUnitIso f. The adjunction identity gives
unit(f) followed by pushforward(f)(e.hom) equal to the structural unit map.
Coefficient naturality then moves e.hom across the coefficient map for f.
For g, naturality in the source identifies coeff(g)(e.hom followed by the
structural map) with inverseImage(g)(forget(e.hom)) followed by the structural
coefficient map for g. Structural unit maps compose because on each open
both composites are the structure-sheaf ring map for g followed by f.
Apply the composite abelian adjunction to identify the composed coefficients;
its left-adjoint comparison is invImageComp g f. Equivalently, apply
coefficientUnit_comp and the naturality and composition comparisons for the
unit pullback isomorphisms. Cancel the forgotten unit isomorphisms to obtain
the equality. This is an equality of sheaf morphisms, independent of degree,
scalars, cartesian squares or cohomology. Identity morphisms give the unit
law; empty schemes and zero rings impose no extra hypothesis.
-/
theorem structuralUnitCoefficient_comp {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X) :
    (invImage g).map (coefficientUnit f (SheafOfModules.unit X.ringCatSheaf)) ≫
        coeff g ((pullbackObjUnitIso f).hom ≫
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) =
      (invImageComp g f).hom.app
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        coeff (g ≫ f) (SheafOfModules.unitToPushforwardObjUnit
          (g ≫ f).toRingCatSheafHom)  := by
  let af := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let ag := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
  let ac := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (g ≫ f).base
  have hc := unit_conjugateEquiv_symm ac (af.comp ag) (𝟙 _)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))
  change ac.unit.app _ ≫ 𝟙 _ = (af.comp ag).unit.app _ ≫ _ at hc
  erw [Category.comp_id] at hc
  apply ((af.comp ag).homEquiv _ _).injective
  have hl : (af.comp ag).homEquiv _ _
      ((invImage g).map (coefficientUnit f (SheafOfModules.unit X.ringCatSheaf)) ≫
        coeff g ((pullbackObjUnitIso f).hom ≫
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app _) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map
            ((pullbackObjUnitIso f).hom ≫
              SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) := by
    erw [Adjunction.comp_homEquiv]
    change af.homEquiv _ _ (ag.homEquiv _ _
      ((invImage g).map (coefficientUnit f _) ≫ coeff g _)) = _
    erw [ag.homEquiv_naturality_left]
    simp only [coefficientUnit, coeff, af, ag]
    erw [Equiv.apply_symm_apply, af.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply]
  erw [hl]
  conv_rhs =>
    erw [(af.comp ag).homEquiv_naturality_right, Adjunction.homEquiv_unit]
  erw [← hc]
  change _ = ac.homEquiv _ _ (coeff (g ≫ f) _)
  simp only [coeff, ac]
  erw [Equiv.apply_symm_apply]
  have hu : (pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫
      (pushforward f).map (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  erw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
  change (SheafOfModules.toSheaf X.ringCatSheaf).map
      ((pullbackPushforwardAdjunction f).unit.app _ ≫
        (pushforward f).map (pullbackObjUnitIso f).hom) ≫ _ = _
  rw [hu]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl


end AlgebraicGeometry.Scheme.Modules
