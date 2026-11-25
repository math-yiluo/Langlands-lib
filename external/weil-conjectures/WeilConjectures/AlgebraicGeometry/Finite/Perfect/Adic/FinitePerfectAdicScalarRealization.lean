/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # The explicit finite coefficient realization on a pro-etale slice

Source: Stacks Project, Tags 03CY, 094T, 0951 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Constant sections of the actual finite coefficient ring on a slice.
Source: Stacks Tags 03CY and 094T.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
def finitePerfectAdicSliceScalar (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) :
    (Functor.const (Over W)ᵒᵖ).obj
        (RingCat.of (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⟶
      ((completedAdicFiniteRing X d n).over W).obj :=
  Functor.whiskerLeft (Over.forget W).op
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))

/-- The constant finite-scalar presentation is locally injective on the slice.
Source: Stacks Tag 03CY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
theorem finitePerfectAdicSliceScalar_injective (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) :
    Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (finitePerfectAdicSliceScalar X d W n) := by
  exact Presheaf.isLocallyInjective_whisker ((ProEt.topology X).over W)
    (ProEt.topology X) (Over.forget W)
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))

/-- The constant finite-scalar presentation is locally surjective on the slice.
Source: Stacks Tag 03CY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
theorem finitePerfectAdicSliceScalar_surjective (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) :
    Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (finitePerfectAdicSliceScalar X d W n) := by
  exact Presheaf.isLocallySurjective_whisker ((ProEt.topology X).over W)
    (ProEt.topology X) (Over.forget W)
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))

/-- Associated module sheaf for fixed finite coefficients on the slice.
Source: Stacks Tag 03CY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
def finitePerfectAdicSliceModules (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) :
    Sheaf ((ProEt.topology X).over W)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⥤
      SheafOfModules.{t + 1} ((completedAdicFiniteRing X d n).over W) :=
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  sheafToPresheaf _ _ ⋙
    ProEtale.finiteCoefficientModulePresheaf (Over W) (completedAdicQuotient d n) ⋙
      PresheafOfModules.sheafification (finitePerfectAdicSliceScalar X d W n)

/-- Fixed finite coefficients and the actual finite ring sheaf give equivalent module
categories on the slice. Source: Stacks Tag 03CY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
instance finitePerfectAdicSliceModules_isEquivalence
    (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) :
    (finitePerfectAdicSliceModules X d W n).IsEquivalence := by
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  exact ProEtale.coefficientRealization_isEquivalence ((ProEt.topology X).over W)
    (completedAdicQuotient d n) ((completedAdicFiniteRing X d n).over W)
    (finitePerfectAdicSliceScalar X d W n)

/-- Arrows over X between weakly etale chart objects are weakly etale.
Source: Stacks Tags 094T and 00XZ.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
theorem finitePerfectAdicChartArrow_weaklyEtale {X : Scheme.{t}} (V : X.Etale)
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) :
    WeaklyEtale f.left := by
  have hc : f.left ≫ (finitePerfectAdicChartObject V U).hom = W.hom :=
    MorphismProperty.Over.w f
  have : WeaklyEtale (f.left ≫ (finitePerfectAdicChartObject V U).hom) :=
    hc.symm ▸ W.prop
  exact WeaklyEtale.of_comp f.left (finitePerfectAdicChartObject V U).hom

/-- Restrict from the chart to W, transport to its slice, realize finite coefficients,
and forget the finite action along the specified completed-ring projection.
Source: Stacks Tags 094T, 0951, 03CY and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
def finitePerfectAdicScalarModules (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    Sheaf (ProEt.topology U.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⥤
      SheafOfModules.{t + 1} ((completedAdicRing X d).over W) :=
  have := ProEt.sliceDense X W
  ProEtale.localizationRestriction
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
      f.left (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))).inverse ⋙
    finitePerfectAdicSliceModules X d W n ⋙
    SheafOfModules.restrictScalars
      (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
        (completedAdicProjection X d n))

/-- Restriction to W and restriction of the completed action are exact; the two
intermediate transports are equivalences. Source: Stacks Tags 03CY and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
theorem finitePerfectAdicScalarModules_exact (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (V : X.Etale)
    (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    (finitePerfectAdicScalarModules X d V U W f n).Additive ∧
      PreservesFiniteLimits (finitePerfectAdicScalarModules X d V U W f n) ∧
      PreservesFiniteColimits (finitePerfectAdicScalarModules X d V U W f n) := by
  have := ProEt.sliceDense X W
  let B := ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))
  let F := ProEtale.localizationRestriction B f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f)
  have : F.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits F := by
    dsimp [F, ProEtale.localizationRestriction]
    infer_instance
  have : PreservesFiniteColimits F := by
    have := (ProEtale.localizationRestrictionLowerStarAdjunction B f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f)).isLeftAdjoint
    infer_instance
  let E := ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) B).inverse
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  have : (finitePerfectAdicSliceModules X d W n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let P := SheafOfModules.restrictScalars
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicProjection X d n))
  let G := SheafOfModules.toSheaf.{t + 1} ((completedAdicRing X d).over W)
  have : PreservesFiniteLimits (P ⋙ G) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{t + 1} ((completedAdicFiniteRing X d n).over W)))
  have : PreservesFiniteColimits (P ⋙ G) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{t + 1} ((completedAdicFiniteRing X d n).over W)))
  have : PreservesFiniteLimits P := preservesFiniteLimits_of_reflects_of_preserves P G
  have : PreservesFiniteColimits P := preservesFiniteColimits_of_reflects_of_preserves P G
  change (F ⋙ E ⋙ finitePerfectAdicSliceModules X d W n ⋙ P).Additive ∧
    PreservesFiniteLimits (F ⋙ E ⋙ finitePerfectAdicSliceModules X d W n ⋙ P) ∧
    PreservesFiniteColimits (F ⋙ E ⋙ finitePerfectAdicSliceModules X d W n ⋙ P)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Termwise localization of the explicit exact realization, without choosing a
functor or module object from an existence theorem. Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-scalar-realization). -/
def finitePerfectAdicScalarRealization (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W)) :=
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  (finitePerfectAdicScalarModules X d V U W f n).mapDerivedCategory

end AlgebraicGeometry.Scheme
