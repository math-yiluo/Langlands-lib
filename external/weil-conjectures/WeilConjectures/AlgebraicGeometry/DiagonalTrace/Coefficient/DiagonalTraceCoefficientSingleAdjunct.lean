/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization

/-! # A single-object comparison for the coefficient adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
  Functor.mapDerivedCategorySingleFunctor Functor.rightDerivedFunctorObjQIso

/-- The derived coefficient adjunct is the ordinary adjunct followed by the cochain unit.

Source: geometric classes proof (3), coefficient-pullback unit normalization;
diagonal tower trace proof (2), coefficient-unit square.
(blueprint: lem-sfb-diagonal-trace-coefficient-single-adjunct).

Proof: the derived coefficient pullback is the exact single-functor comparison
followed by the localization of its ordinary isomorphism. The canonical derived
adjunction unit on a cochain complex is its ordinary unit followed by the right
cochain unit. Evaluate on a single object and use naturality for the ordinary
coefficient isomorphism. This gives the ordinary adjunct followed by the canonical
right-derived single-object comparison. -/
theorem diagonalTrace_coefficient_single_adjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l E f) :
    let := p.base.kinjective X
    let := p.model.geometry.pushAdditive
    ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
        (p.model.coefficientPullback.derivedIso l E).hom) =
      (DerivedCategory.singleFunctor
          (SpTowerClasses.Systems S (SpTowerClasses.Arings l E S)) 0).map
        ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
          p.model.coefficientPullback.iso.hom) ≫
        diagonalTraceRightSingle p.model.geometry.push
          (canonicalDiagonalRightDerived p.model.geometry.push)
          (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)) := by
  let := p.base.kinjective X
  let := p.model.geometry.pushAdditive
  let := p.model.geometry.pullAdditive
  let := p.model.geometry.pullLimits
  let := p.model.geometry.pullColimits
  dsimp only
  exact adjunct_single p.model.geometry.ordinaryAdjunction
    (SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S))
    (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))
    p.model.coefficientPullback.iso.hom

end AlgebraicGeometry.ProEtale.DiagonalTrace
