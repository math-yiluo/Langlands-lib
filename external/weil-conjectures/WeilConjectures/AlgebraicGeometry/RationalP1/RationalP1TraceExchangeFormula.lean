/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The native formula for the second projective-line exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.RationalP1

local instance instEssentiallySmallProfinite_rationalP1TraceExchangeFormula
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  firstProjection secondProjection square upperStarFromPoint
  DerivedCategory.monoidalClosed Mod.monoidalClosed CondensedRing.upperStar

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward

/-- The second trace exchange is the native exchange followed by the direct
image of its line comparison. -/
theorem secondTraceExchange_eq_native
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    secondTraceExchange l c k p hpl Y =
      (condensedAmbientExchange (coefficient l c).X (square Y)).app _ ≫
        (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
          (firstLineComparisonForTrace l c k p hpl Y).hom := by
  unfold secondTraceExchange secondPretraceExchangeMap
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map,
    Category.id_comp, Category.comp_id]
  coefficient_congr

end AlgebraicGeometry.ProEtale.RationalP1
