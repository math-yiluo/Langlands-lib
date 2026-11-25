/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
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
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Completed compact-support exchange for a chosen compactification

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
Definition 1939, main-20261015 (blueprint: def-cbc-completed-exchange-map).

The proper factor is the specified strict-tower exchange, followed by direct
image of the canonical completed open comparison. The two Cartesian squares
retain the chosen base-changed compactification and its projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The completed compact-support exchange attached to a compactification and its
base change. `properSquare` and `openSquare` specify the lower proper and upper
open Cartesian squares, respectively; their outer square is the given compact-support
square. The target compactification is thus the base change of the source one,
with the supplied projection `gbar`, rather than an unrelated factorization.

The coefficient datum contains all Noetherian, finite-quotient, torsion and
perfectness hypotheses. `K` belongs to the intrinsic derived-complete category,
with any finite generating tuple of the ideal (including the empty tuple).
A compactification already implies that `f` is separated and locally of finite
type; `[QuasiCompact f]` supplies exactly the remaining finite-type condition.
The quasi-compactness needed by open exchange then follows from properness of
the compactification map.

The first factor is `completedExchange`: derived limit of the strict projection
map, followed by derived limit of the specified strict tower exchange and the
inverse direct-image/derived-limit comparison. The strict exchange is the
projection-formula realization H inverse, reduction of the ambient mate, H prime;
no lift is chosen from its individual finite evaluations. On witnessed reductions
it is precisely `completedBaseChangeMap`. The second factor is direct image of
`cbcDatumCompletedExchange`, the normalized completed extension-by-zero comparison.
No invertibility or compactification-independence assertion is part of this definition.

Source: blueprint main-20261015, Definition 1939; strict-tower expansion of the
same definition, order 1588 (blueprint: def-cbc-completed-exchange-map). -/
def completedCompactSupportExchange
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :
    (d.completedPull g).obj
        ((d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj)) ⟶
      (d.push c'.g).obj
        ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).obj
          ((d.completedPull g').obj K.obj)) :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  d.completedExchange properSquare
      ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj) ≫
    (d.push c'.g).map ((cbcDatumCompletedExchange d openSquare r a ha).app K)

end AlgebraicGeometry.Scheme
