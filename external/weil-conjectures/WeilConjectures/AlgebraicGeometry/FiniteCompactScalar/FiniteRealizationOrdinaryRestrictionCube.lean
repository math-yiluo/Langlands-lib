/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport

/-! # The ordinary realization, restriction, and direct-image cube

Source: Stacks Tags 00YV and 03D1; Step 1 of the realization/restriction cube.
(blueprint: lem-finite-realization-ordinary-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

attribute [local implicit_reducible]
  AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage

/-- The realization/restriction cube commutes before passing to derived categories.
Source: Stacks Tags 00YV and 03D1; section-normalized intrinsic realization.
(blueprint: lem-finite-realization-ordinary-restriction-cube).
Proof: precompose by the invertible ordinary coefficient comparison and evaluate
on a section. Surjectivity of the realization unit expresses that section as a
unit section. The coefficient comparisons preserve its underlying section, and
the two direct-image comparisons take unit sections to the corresponding target
unit sections. Their resulting unit maps agree on underlying abelian sheaves.
This proof works without properness or restrictions on the coefficient map,
including zero rings and empty schemes. -/
theorem realizationRestriction_ordinary_directImage_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (proEtaleConstantModuleDirectImage g A).map
        ((sfRealizationRestriction Z φ).hom.app M) ≫
      (sfIntrinsicDirectImageComparison g A).hom.app ((sfFixedRestriction Z φ).obj M) =
    (proEtaleCoefficientDirectImageComparison g φ).inv.app
        ((sfIntrinsicModuleEquivalence Z B).functor.obj M) ≫
      (proEtaleCoefficientRestrictScalars Y φ).map
        ((sfIntrinsicDirectImageComparison g B).hom.app M) ≫
      (sfRealizationRestriction Y φ).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).obj M) := by
  have hr (T : Scheme.{u})
      (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
      (W : T.ProEtᵒᵖ) (n : ((sfIntrinsicModuleEquivalence T B).functor.obj N).val.obj W) :=
    (sfRealizationRestriction_existsUnique T φ).exists.choose_spec N W n
  apply (cancel_epi ((proEtaleCoefficientDirectImageComparison g φ).hom.app
    ((sfIntrinsicModuleEquivalence Z B).functor.obj M))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  ext W x
  let U := (proEtaleBaseChange g).op.obj W
  let η := ((PresheafOfModules.evaluation _ U).mapIso
    ((AlgebraicGeometry.Scheme.intrinsicUnitIso Z B).app M)).toLinearEquiv
  obtain ⟨m, hm⟩ := η.surjective x
  change M.obj.obj U at m
  change sfIntrinsicRealizationUnit Z B M U m = x at hm
  subst x
  change ((sfIntrinsicDirectImageComparison g A).hom.app
      ((sfFixedRestriction Z φ).obj M)).val.app W
      (((sfRealizationRestriction Z φ).hom.app M).val.app U
        (((proEtaleCoefficientDirectImageComparison g φ).hom.app _).val.app W _)) =
    ((sfRealizationRestriction Y φ).hom.app _).val.app W
      (((sfIntrinsicDirectImageComparison g B).hom.app M).val.app W _)
  have hc := (proEtaleCoefficientDirectImageComparison_existsUnique g φ).choose_spec.1
    ((sfIntrinsicModuleEquivalence Z B).functor.obj M) W
    (sfIntrinsicRealizationUnit Z B M U m)
  change (((proEtaleCoefficientDirectImageComparison g φ).hom.app _).val.app W _) = _ at hc
  rw [hc]
  change ((sfIntrinsicDirectImageComparison g A).hom.app
      ((sfFixedRestriction Z φ).obj M)).val.app W
      (((sfRealizationRestriction Z φ).hom.app M).val.app U _) =
    ((sfRealizationRestriction Y φ).hom.app _).val.app W
      (((sfIntrinsicDirectImageComparison g B).hom.app M).val.app W _)
  have hrZ := hr Z M U (sfIntrinsicRealizationUnit Z B M U m)
  dsimp only [sfRealizationRestriction]
  rw [hrZ]
  have hrY := hr Y
    ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).obj M) W
    (((sfIntrinsicDirectImageComparison g B).hom.app M).val.app W
      (sfIntrinsicRealizationUnit Z B M U m))
  rw [hrY]
  have ha := (sfIntrinsicDirectImageComparison_existsUnique g A).exists.choose_spec
    ((sfFixedRestriction Z φ).obj M) W m
  have hb := (sfIntrinsicDirectImageComparison_existsUnique g B).exists.choose_spec M W m
  erw [ha, hb]
  rfl

end AlgebraicGeometry.Scheme.FiniteCompactScalar
