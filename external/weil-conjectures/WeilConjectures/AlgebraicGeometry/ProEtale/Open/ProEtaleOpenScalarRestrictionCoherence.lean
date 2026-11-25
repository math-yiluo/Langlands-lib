/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Coherent scalar restriction for open extension by zero

The comparisons are the `sfOpenRestriction` and its exact termwise
localization. Normalization is expressed on the open adjunction unit: on each
nonzero summand of the defining extension presheaf it is the identity; maps from
all remaining values, which are zero, are unique. Thus this unit equation is
precisely the pre-sheafification normalization, without a choice of stalks.

## References

* Tag 04VG
* Stacks Tags 03DI and 03CY
* Stacks Tags 03DI and 03DA
* Stacks Tags 03DI and 00YV
* Stacks Tag 015F
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- The normalized realization comparison is the identity on sections. -/
private theorem realization_hom_apply (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : T.ProEtᵒᵖ) (x : ((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj V) :
    ((sfRealizationRestriction T φ).hom.app M).val.app V x = x :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose_spec M V x

/-- The inverse normalized realization comparison is the identity on sections. -/
private theorem realization_inv_apply (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : T.ProEtᵒᵖ)
    (x : ((sfIntrinsicModuleEquivalence T A).functor.obj
      ((sfFixedRestriction T φ).obj M)).val.obj V) :
    ((sfRealizationRestriction T φ).inv.app M).val.app V x = x := by
  have hh := congrArg (fun t ↦ t.val.app V x)
    ((sfRealizationRestriction T φ).inv_hom_id_app M)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at hh
  rw [← realization_hom_apply T φ M V (((sfRealizationRestriction T φ).inv.app M).val.app V x)]
  exact hh

omit [Finite A] [Finite B] in
/-- Restriction to an open commutes strictly with fixed scalar restriction on maps. -/
private theorem restriction_fixed_map {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) {P Q : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))}
    (f : P ⟶ Q) :
    (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfFixedRestriction Z φ).map f) =
      (sfFixedRestriction X φ).map
        ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map f) := by
  rfl

omit [Finite A] [Finite B] [Finite C] in
/-- The scalar compositor is the identity on sections. -/
private theorem coefficientComp_hom_apply (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((sfCoefficientRestrictionComp T φ ψ).hom.app M).val.app V x = x :=
  (pbcRestrictComp_exists _ _ _
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm).exists.choose_spec
      M V x

/-- Composition law for the inverse normalized realization comparisons. -/
private theorem realization_inv_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfRealizationRestriction T φ).inv.app ((sfFixedRestriction T ψ).obj N) ≫
      (proEtaleCoefficientRestrictScalars T φ).map
        ((sfRealizationRestriction T ψ).inv.app N) ≫
      (sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj N) =
    (sfRealizationRestriction T (ψ.comp φ)).inv.app N := by
  ext V x
  refine (coefficientComp_hom_apply T φ ψ _ V _).trans ?_
  refine (realization_inv_apply T ψ N V _).trans ?_
  refine (realization_inv_apply T φ _ V x).trans ?_
  exact (realization_inv_apply T (ψ.comp φ) N V x).symm

attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction
attribute [local irreducible] sfIntrinsicModuleEquivalence

omit [Finite A] [Finite B] in
/-- Unit normalization of the fixed-scalar open comparison: after the open
adjunction unit, its restriction to the open is restriction of scalars of the
open adjunction unit. -/
private theorem fixed_normalized {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
        ((sfFixedRestriction X φ).obj N) ≫
      (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfFixedOpenRestriction j φ).hom.app N) =
    (sfFixedRestriction X φ).map
      ((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app N) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ.ulift).comp
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ.ulift)) N
  apply ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ.ulift).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  erw [h, Adjunction.unit_naturality]
  rfl

omit [Finite A] [Finite B] [Finite C] in
/-- Cocycle for the fixed-scalar open comparisons. -/
private theorem fixed_open_comp {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (ψ : B →+* C)
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfFixedOpenRestriction j (ψ.comp φ)).hom.app N =
      (sfFixedOpenRestriction j φ).hom.app ((sfFixedRestriction X ψ).obj N) ≫
        (sfFixedRestriction Z φ).map ((sfFixedOpenRestriction j ψ).hom.app N) := by
  apply ((ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [fixed_normalized j (ψ.comp φ) N, ← Category.assoc, fixed_normalized j φ]
  rw [restriction_fixed_map, ← Functor.map_comp, fixed_normalized j ψ N]
  rfl

/-- Composition law for the normalized realization comparisons. -/
private theorem realization_hom_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj N) ≫
      (sfRealizationRestriction T (ψ.comp φ)).hom.app N =
    (proEtaleCoefficientRestrictScalars T φ).map
        ((sfRealizationRestriction T ψ).hom.app N) ≫
      (sfRealizationRestriction T φ).hom.app ((sfFixedRestriction T ψ).obj N) := by
  have h := realization_inv_comp T φ ψ N
  rw [← cancel_epi ((sfRealizationRestriction T φ).inv.app ((sfFixedRestriction T ψ).obj N) ≫
    (proEtaleCoefficientRestrictScalars T φ).map ((sfRealizationRestriction T ψ).inv.app N))]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id_app, ← Functor.map_comp_assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- The realization of the inverse realization comparison, expressed by the
realization comparison and the counits of the realization equivalences. -/
private theorem inverseRealization_functor_map (T : Scheme.{u}) (φ : A →+* B)
    (M : proEtaleRingModules T (proEtaleConstantRing T B)) :
    (sfIntrinsicModuleEquivalence T A).functor.map
        ((sfInverseRealizationRestriction T φ).hom.app M) =
      (sfIntrinsicModuleEquivalence T A).counitIso.hom.app
          ((proEtaleCoefficientRestrictScalars T φ).obj M) ≫
        (proEtaleCoefficientRestrictScalars T φ).map
          ((sfIntrinsicModuleEquivalence T B).counitIso.inv.app M) ≫
        (sfRealizationRestriction T φ).hom.app
          ((sfIntrinsicModuleEquivalence T B).inverse.obj M) := by
  simp only [sfInverseRealizationRestriction, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, Functor.map_comp]
  rw [← Equivalence.counit_app_functor, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, Equivalence.counit_naturality]
  rfl

/-- Composition law for the inverse realization comparisons. -/
private theorem inverse_realization_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) :
    (sfIntrinsicModuleEquivalence T A).inverse.map
        ((sfCoefficientRestrictionComp T φ ψ).hom.app M) ≫
      (sfInverseRealizationRestriction T (ψ.comp φ)).hom.app M =
    (sfInverseRealizationRestriction T φ).hom.app
        ((proEtaleCoefficientRestrictScalars T ψ).obj M) ≫
      (sfFixedRestriction T φ).map ((sfInverseRealizationRestriction T ψ).hom.app M) := by
  apply (sfIntrinsicModuleEquivalence T A).functor.map_injective
  simp only [Functor.map_comp, inverseRealization_functor_map]
  rw [Equivalence.counit_naturality_assoc]
  erw [← (sfCoefficientRestrictionComp T φ ψ).hom.naturality_assoc,
    realization_hom_comp T φ ψ ((sfIntrinsicModuleEquivalence T C).inverse.obj M)]
  simp only [Category.assoc]
  erw [← (sfRealizationRestriction T φ).hom.naturality]
  simp only [Functor.comp_map]
  rw [inverseRealization_functor_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (proEtaleCoefficientRestrictScalars T φ)
    ((sfIntrinsicModuleEquivalence T B).counitIso.inv.app _), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Realization of the fixed-scalar identity restriction comparison is the identity:
that comparison is the identity on every section. -/
private theorem fixedRestrictionId_realization (T : Scheme.{u}) (R : Type u) [CommRing R]
    [Finite R] (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) :
    (sfIntrinsicModuleEquivalence T R).functor.map ((sfOpenFixedRestrictionId T R).hom.app N) =
      𝟙 _ := by
  have : (sfOpenFixedRestrictionId T R).hom.app N = 𝟙 N := rfl
  erw [this]
  exact CategoryTheory.Functor.map_id _ _

/-- The canonical identity coefficient comparison is the identity on sections. -/
private theorem coefficientRestrictionId_apply (T : Scheme.{u}) (R : Type u) [CommRing R]
    [Finite R] (M : proEtaleRingModules T (proEtaleConstantRing T R)) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((sfOpenCoefficientRestrictionId T R).hom.app M).val.app V x = x := by
  have h : (sfOpenCoefficientRestrictionId T R).hom.app M =
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)).map
          ((sfIntrinsicModuleEquivalence T R).counitIso.inv.app M) ≫
        (sfRealizationRestriction T (RingHom.id R)).hom.app
          ((sfIntrinsicModuleEquivalence T R).inverse.obj M) ≫
        (sfIntrinsicModuleEquivalence T R).counitIso.hom.app M := by
    simp only [sfOpenCoefficientRestrictionId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, fixedRestrictionId_realization]
    erw [Category.id_comp]
  rw [h]
  refine (congrArg (fun y ↦ ((sfIntrinsicModuleEquivalence T R).counitIso.hom.app M).val.app V y)
    (realization_hom_apply T (RingHom.id R) _ V _)).trans ?_
  exact congrArg (fun t ↦ t.val.app V x)
    ((sfIntrinsicModuleEquivalence T R).counitIso.inv_hom_id_app M)

/-- The identity scalar compositor is scalar restriction of the canonical identity
comparison. -/
private theorem restriction_id_comp (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules T (proEtaleConstantRing T R)) :
    (sfCoefficientRestrictionComp T (RingHom.id R) (RingHom.id R)).hom.app M =
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)).map
        ((sfOpenCoefficientRestrictionId T R).hom.app M) := by
  ext V x
  refine (coefficientComp_hom_apply T (RingHom.id R) (RingHom.id R) M V x).trans ?_
  exact (coefficientRestrictionId_apply T R M V x).symm

/-- The inverse realization comparison is the mate of the inverse realization
comparison along the realization units. -/
private theorem realization_unit_inverse (T : Scheme.{u}) (φ : A →+* B)
    (X : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (sfIntrinsicModuleEquivalence T A).unitIso.hom.app ((sfFixedRestriction T φ).obj X) ≫
      (sfIntrinsicModuleEquivalence T A).inverse.map
        ((sfRealizationRestriction T φ).inv.app X) ≫
      (sfInverseRealizationRestriction T φ).hom.app
        ((sfIntrinsicModuleEquivalence T B).functor.obj X) =
    (sfFixedRestriction T φ).map ((sfIntrinsicModuleEquivalence T B).unitIso.hom.app X) := by
  apply (sfIntrinsicModuleEquivalence T A).functor.map_injective
  simp only [Functor.map_comp, inverseRealization_functor_map]
  erw [Equivalence.counit_naturality_assoc, Equivalence.functor_unit_comp_assoc,
    Equivalence.counitInv_app_functor]
  erw [(sfRealizationRestriction T φ).hom.naturality, Iso.inv_hom_id_app_assoc]
  rfl

/-- The open comparison in fixed-scalar coordinates: after the realization unit
and the inverse realization comparison, it is the fixed-scalar open comparison. -/
private theorem open_inverse {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (M : proEtaleRingModules U (proEtaleConstantRing U B)) :
    (sfIntrinsicModuleEquivalence Z A).unitIso.hom.app
        ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          ((sfIntrinsicModuleEquivalence U A).inverse.obj
            ((proEtaleCoefficientRestrictScalars U φ).obj M))) ≫
      (sfIntrinsicModuleEquivalence Z A).inverse.map ((sfOpenRestriction j φ).hom.app M) ≫
      (sfInverseRealizationRestriction Z φ).hom.app ((sfIntrinsicExtensionByZero j B).obj M) =
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfInverseRealizationRestriction U φ).hom.app M) ≫
      (sfFixedOpenRestriction j φ).hom.app ((sfIntrinsicModuleEquivalence U B).inverse.obj M) ≫
      (sfFixedRestriction Z φ).map ((sfIntrinsicModuleEquivalence Z B).unitIso.hom.app
        ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).obj
          ((sfIntrinsicModuleEquivalence U B).inverse.obj M))) := by
  simp only [sfOpenRestriction, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [Equivalence.unit_naturality_assoc, Equivalence.unit_naturality_assoc]
  congr 2
  exact realization_unit_inverse Z φ _

omit [Finite A] in
/-- The unit of the intrinsic extension-by-zero adjunction, in terms of the
fixed-scalar open adjunction unit and the realization unit and counit. -/
private theorem intrinsic_unit {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (R : Type u) [CommRing R] [Finite R]
    (N : proEtaleRingModules U (proEtaleConstantRing U R)) :
    (sfIntrinsicExtensionByZeroAdjunction j R).unit.app N =
      (sfIntrinsicModuleEquivalence U R).counitIso.inv.app N ≫
        (sfIntrinsicModuleEquivalence U R).functor.map
          ((ProEtale.openImmersionLowerShriekAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).unit.app
              ((sfIntrinsicModuleEquivalence U R).inverse.obj N) ≫
            (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).map
              ((sfIntrinsicModuleEquivalence Z R).unitIso.hom.app
                ((ProEtale.openImmersionLowerShriek
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).obj
                  ((sfIntrinsicModuleEquivalence U R).inverse.obj N)))) := by
  simp only [sfIntrinsicExtensionByZeroAdjunction, Adjunction.comp_unit_app,
    Equivalence.toAdjunction_unit, Functor.map_comp, Category.assoc]
  rfl

/-- The open comparison is normalized by the open adjunction units. -/
private theorem open_normalized {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) : SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) := by
  intro M
  have hfix :
      (ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
          ((sfIntrinsicModuleEquivalence U A).inverse.obj
            ((proEtaleCoefficientRestrictScalars U φ).obj M)) ≫
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
          ((sfIntrinsicModuleEquivalence Z A).unitIso.hom.app
            ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
              ((sfIntrinsicModuleEquivalence U A).inverse.obj
                ((proEtaleCoefficientRestrictScalars U φ).obj M))) ≫
            (sfIntrinsicModuleEquivalence Z A).inverse.map ((sfOpenRestriction j φ).hom.app M) ≫
            (sfInverseRealizationRestriction Z φ).hom.app
              ((sfIntrinsicExtensionByZero j B).obj M)) =
      (sfInverseRealizationRestriction U φ).hom.app M ≫
        (sfFixedRestriction U φ).map
          ((ProEtale.openImmersionLowerShriekAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app
              ((sfIntrinsicModuleEquivalence U B).inverse.obj M) ≫
            (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
              ((sfIntrinsicModuleEquivalence Z B).unitIso.hom.app
                ((ProEtale.openImmersionLowerShriek
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).obj
                  ((sfIntrinsicModuleEquivalence U B).inverse.obj M)))) := by
    rw [open_inverse, Functor.map_comp, Functor.map_comp]
    erw [Adjunction.unit_naturality_assoc,
      reassoc_of% fixed_normalized j φ ((sfIntrinsicModuleEquivalence U B).inverse.obj M),
      restriction_fixed_map, Functor.map_comp]
  have hF := congrArg (sfIntrinsicModuleEquivalence U A).functor.map hfix
  simp only [Functor.map_comp] at hF
  rw [intrinsic_unit, intrinsic_unit]
  simp only [sfIntrinsicOpenRestriction, sfOpenRestrictionCoefficientSquare, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map, Iso.refl_hom,
    NatTrans.id_app, Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hF, inverseRealization_functor_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have n1 := (sfRealizationRestriction U φ).inv.naturality
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app
        ((sfIntrinsicModuleEquivalence U B).inverse.obj M))
  have n2 := (sfRealizationRestriction U φ).inv.naturality
    ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
      ((sfIntrinsicModuleEquivalence Z B).unitIso.hom.app
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).obj
          ((sfIntrinsicModuleEquivalence U B).inverse.obj M))))
  simp only [Functor.comp_map] at n1 n2
  erw [n2, reassoc_of% n1, Iso.hom_inv_id_app_assoc]

/-- The comparison is the unique comparison inducing identity on the
extension presheaves, equivalently satisfying the displayed open-unit equation. -/
theorem sfOpenRestriction_normalized_unique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) ∧
      ∀ e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
          sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ,
        SfOpenRestrictionNormalized j φ e → e = sfOpenRestriction j φ := by
  refine ⟨open_normalized j φ, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((sfIntrinsicExtensionByZeroAdjunction j A).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_mono ((sfOpenRestrictionCoefficientSquare j φ).hom.app
    ((sfIntrinsicExtensionByZero j B).obj M))).mp
  simpa only [Category.assoc] using (he M).trans ((open_normalized j φ) M).symm

/-- The sheaf comparison cocycle, including both canonical scalar associators. -/
theorem sfOpenRestriction_coefficient_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
    (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).hom.app M) ≫
      (sfOpenRestriction j (ψ.comp φ)).hom.app M =
    (sfOpenRestriction j φ).hom.app ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z φ).map
        ((sfOpenRestriction j ψ).hom.app M) ≫
      (sfCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).obj M) := by
  let N := (sfIntrinsicModuleEquivalence U C).inverse.obj M
  have hn₁ := (sfRealizationRestriction Z φ).inv.naturality
    ((ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
        ((sfInverseRealizationRestriction U ψ).hom.app M))
  have hn₂ := (sfRealizationRestriction Z φ).inv.naturality
    ((sfFixedOpenRestriction j ψ).hom.app N)
  have hn₃ := (sfFixedOpenRestriction j φ).hom.naturality
    ((sfInverseRealizationRestriction U ψ).hom.app M)
  simp only [Functor.comp_map] at hn₁ hn₂ hn₃
  simp only [sfOpenRestriction, sfIntrinsicExtensionByZero,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at hn₁ hn₂ hn₃ ⊢
  slice_rhs 3 4 => exact hn₁.symm
  slice_rhs 4 5 => exact hn₂.symm
  slice_rhs 5 7 => exact realization_inv_comp Z φ ψ _
  simp only [← (sfIntrinsicModuleEquivalence Z A).functor.map_comp_assoc]
  congr 2
  slice_rhs 2 3 => exact hn₃.symm
  simp only [Category.assoc]
  slice_rhs 3 4 => exact (fixed_open_comp j φ ψ N).symm
  simp only [← Functor.map_comp_assoc]
  rw [inverse_realization_comp]

/-- The identity coefficient law on module sheaves, with canonical identifications. -/
theorem sfOpenRestriction_coefficient_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
    (sfOpenRestriction j (RingHom.id R)).hom.app M ≫
        (sfOpenCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).obj M) =
      (sfIntrinsicExtensionByZero j R).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M) := by
  have hc := sfOpenRestriction_coefficient_comp j (RingHom.id R) (RingHom.id R) M
  have hn := (sfOpenRestriction j (RingHom.id R)).hom.naturality
    ((sfOpenCoefficientRestrictionId U R).hom.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [restriction_id_comp, restriction_id_comp] at hc
  change (sfIntrinsicExtensionByZero j R).map
      ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M)) ≫
      (sfOpenRestriction j (RingHom.id R)).hom.app M = _ at hc
  rw [hn] at hc
  have hmap := (cancel_epi ((sfOpenRestriction j (RingHom.id R)).hom.app
    ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).obj M))).mp hc
  rw [← Functor.map_comp] at hmap
  ext V x
  exact congrArg (fun f ↦ f.val.app V x) hmap.symm

/-- The prescribed comparison on unbounded derived categories: exact termwise
localization of the already normalized sheaf comparison, with the exact-functor
composition identifications at its endpoints. -/
def sfOpenRestrictionDerived {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars U φ).mapDerivedCategory ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory ⋙
        (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)

/-- Canonical identification of derived identity coefficient restriction with the
identity functor, localized from the sectionwise identity comparison. -/
def sfOpenDerivedCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    (proEtaleCoefficientRestrictScalars T (RingHom.id R)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (sfOpenCoefficientRestrictionId T R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The prescribed coefficient cocycle on the entire unbounded derived category. -/
theorem sfOpenRestriction_derived_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (K : proEtaleDerivedCategory U C) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫
      (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K =
    (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) := by
  have hq (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
      (sfIntrinsicExtensionByZero j A).map
          ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫
        (sfOpenRestriction j φ).hom.app
          ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
        (proEtaleCoefficientRestrictScalars Z φ).map
          ((sfOpenRestriction j ψ).hom.app M) =
      (sfOpenRestriction j (ψ.comp φ)).hom.app M ≫
        (sfCoefficientRestrictionComp Z φ ψ).inv.app
          ((sfIntrinsicExtensionByZero j C).obj M) := by
    have h := congrArg (fun t ↦
      (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫ t ≫
      (sfCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).obj M))
      (sfOpenRestriction_coefficient_comp j φ ψ M)
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (proEtaleCoefficientRestrictScalars U ψ) (proEtaleCoefficientRestrictScalars U φ)
    (proEtaleCoefficientRestrictScalars U (ψ.comp φ))
    (proEtaleCoefficientRestrictScalars Z ψ) (proEtaleCoefficientRestrictScalars Z φ)
    (proEtaleCoefficientRestrictScalars Z (ψ.comp φ))
    (sfIntrinsicExtensionByZero j C) (sfIntrinsicExtensionByZero j B)
    (sfIntrinsicExtensionByZero j A)
    (sfOpenRestriction j ψ) (sfOpenRestriction j φ)
    (sfOpenRestriction j (ψ.comp φ))
    (sfCoefficientRestrictionComp U φ ψ).symm
    (sfCoefficientRestrictionComp Z φ ψ).symm hq
  have hk := congrArg (fun e ↦ e.hom.app K) hd
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.mapDerivedCategoryNatIso_symm] at hk
  change (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).inv.app K) ≫
      (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) =
    (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) at hk
  have h := congrArg (fun t ↦
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
      ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫ t ≫
    (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
      ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K)) hk
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h.symm

/-- The identity coefficient comparison on all unbounded derived objects. -/
theorem sfOpenRestriction_derived_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (K : proEtaleDerivedCategory U R) :
    (sfOpenRestrictionDerived j (RingHom.id R)).hom.app K ≫
        (sfOpenDerivedCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj K) =
      (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
        ((sfOpenDerivedCoefficientRestrictionId U R).hom.app K) := by
  have hi (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
      (sfOpenRestriction j (RingHom.id R)).inv.app M ≫
        (sfIntrinsicExtensionByZero j R).map
          ((sfOpenCoefficientRestrictionId U R).hom.app M) =
      (sfOpenCoefficientRestrictionId Z R).hom.app
        ((sfIntrinsicExtensionByZero j R).obj M) := by
    rw [← sfOpenRestriction_coefficient_id j R M]
    simp
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_id
    (sfOpenRestriction j (RingHom.id R)).symm
    (sfOpenCoefficientRestrictionId U R) (sfOpenCoefficientRestrictionId Z R) hi K
  have hs : Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction j (RingHom.id R)).symm =
      (sfOpenRestrictionDerived j (RingHom.id R)).symm := by
    apply Iso.ext
    simp only [sfOpenRestrictionDerived, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at hd
  rw [← cancel_epi ((sfOpenRestrictionDerived j (RingHom.id R)).inv.app K)]
  simpa only [sfOpenDerivedCoefficientRestrictionId, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.symm_hom] using hd.symm

end AlgebraicGeometry.Scheme
