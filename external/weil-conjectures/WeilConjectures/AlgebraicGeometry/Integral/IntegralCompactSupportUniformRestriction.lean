/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.Proper.ProperBaseChangeFourCorners
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeGeometryFibreBound
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedConstructiblePreservation
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Integral compact support preserves the compatible uniform constructible category

The three functor properties below are tested on the full compatible uniform subcategory.
Fullness gives the restricted functor, and its triangles and shifts are inherited.

## References

* Stacks Tags 0GL0 and 095U
* Bhatt--Scholze, Lemmas 6.7.2 and 6.7.7
* Stacks 098T
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme

/-- Canonical completed-coefficient inverse image, reusing the finite-quotient
comparison and the constant-section-normalized presentation of the completed ring. -/
noncomputable def cbcCompletedCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcCompletedComparison Y d).symm ≪≫
    fourCornerCoefficientIso f
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } ≪≫
    pbcCompletedComparison X d

/-- Both completed coefficient comparisons have the same positive-quotient projections. -/
private theorem coefficientIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    cbcCompletedCoefficientIso f d = d.integralRingIso f := by
  apply Iso.ext
  rw [← cbcDatumCoefficient_eq d f]
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  apply limit.hom_ext
  rintro ⟨n⟩
  change (cbcCompletedCoefficientIso f d).hom ≫ pbcAdicProjection X d n = _
  dsimp only [cbcCompletedCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [Category.assoc]
  change L.map (pbcCompletedComparison Y d).inv ≫
    (fourCornerCoefficientIso f dd).hom ≫
      (pbcCompletedComparison X d).hom ≫ limit.π _ (Opposite.op n) = _
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc (fourCornerCoefficientIso f dd).hom]
  have hfc := fourCornerProjectionComm f dd n
  dsimp only [adicDatumProjection] at hfc
  erw [hfc]
  simp only [Category.assoc]
  rw [← Category.assoc, ← L.map_comp]
  change L.map ((pbcCompletedComparison Y d).inv ≫ limit.π _ (Opposite.op n)) ≫ _ = _
  erw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc, completedCoefficientMap, limit.lift_π]
  rfl

private theorem coefficientSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (V : Y.ProEtᵒᵖ) (a : A) :
    (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).hom.app V (pbcCompletedSection Y d V a) =
      pbcCompletedSection X d ((proEtaleBaseChange f).op.obj V) a := by
  have he : proEtaleRingDirectImageMap f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (cbcCompletedCoefficientIso f d) =
        completedCoefficientDirectImageMap f d := by
    rw [coefficientIso_eq]
    unfold proEtaleRingDirectImageMap completedCoefficientDirectImageMap
    rw [cbcDatumCoefficient_eq]
  rw [he]
  exact pbcCompletedSection_directImage f d V a

private theorem completedModulePushLinear {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).Linear A := by
  constructor
  intro M N h a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change pbcCompletedSection X d ((proEtaleBaseChange f).op.obj V) a •
      h.val.app ((proEtaleBaseChange f).op.obj V) x =
    (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).hom.app V (pbcCompletedSection Y d V a) •
        h.val.app ((proEtaleBaseChange f).op.obj V) x
  rw [coefficientSections]

private theorem completedModulePullLinear {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleRingModulePullback f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).Linear A := by
  have := completedModulePushLinear f d
  exact (proEtaleRingModuleAdjunction f _ _ _).left_adjoint_linear

end AlgebraicGeometry.Scheme
