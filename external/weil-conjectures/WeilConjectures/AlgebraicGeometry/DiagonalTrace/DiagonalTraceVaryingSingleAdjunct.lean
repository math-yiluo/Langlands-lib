/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientSingleAdjunct
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingSingleSquare

/-! # The varying comparison on a coefficient adjunction unit -/

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
  Functor.mapDerivedCategorySingleFunctor
  Functor.rightDerivedFunctorObjQIso

/-- The varying comparison transports the coefficient adjunct through degree zero.

Source: diagonal tower trace proof (2), coefficient-unit compatibility, and
geometric classes proof (3), normalized coefficient pullback.
(blueprint: lem-sfb-diagonal-trace-varying-single-adjunct).

Proof: extend the varying comparison's normalization from K-injective complexes
using the supplied acyclicity. The single-complex comparison for this exact square
identifies the ordinary right-derived map. The canonical derived adjunction unit
on a single object is the ordinary adjunct followed by that right-derived map.
Naturality of the exact single-object comparisons and cancellation give the stated
identity. This uses the actual coefficient pullback and its derived localization. -/
theorem diagonalTrace_varying_single_adjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l E f)
    (hacyc : ∀ I : CochainComplex (SpTowerClasses.Systems X
      (SpTowerClasses.Arings l E X)) ℤ, I.IsKInjective →
      IsIso (p.Rt.η.app ((p.restrictionX.F.mapHomologicalComplex (.up ℤ)).obj I))) :
    let := p.base.kinjective X
    let := p.model.geometry.pushAdditive
    let := p.restrictionS.additive
    let := p.restrictionX.additive
    let := p.restrictionX.limits
    let := p.restrictionX.colimits
    let := p.restrictionS.limits
    let := p.restrictionS.colimits
    DiagonalSingleUnitCompatible (diagonalTraceSystemPush l f)
      p.restrictionX.F p.restrictionS.F p.Rt
      (SpTowerShriek.push l E p.base p.model.geometry) p.varying
      (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))
      (SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S))
      ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
        (p.model.coefficientPullback.derivedIso l E).hom)
      (p.restrictionS.F.map ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
        p.model.coefficientPullback.iso.hom) ≫ p.varyingOrdinary.hom.app
          (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))) := by
  let := p.base.kinjective X
  let := p.model.geometry.pushAdditive
  let := p.restrictionS.additive
  let := p.restrictionX.additive
  let := p.restrictionS.limits
  let := p.restrictionS.colimits
  let := p.restrictionX.limits
  let := p.restrictionX.colimits
  dsimp only
  exact singleUnitCompatible_of_singleSquare p.model.geometry.push
    (diagonalTraceSystemPush l f) p.restrictionX.F p.restrictionS.F
    (canonicalDiagonalRightDerived p.model.geometry.push) p.Rt p.varyingOrdinary p.varying
    (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))
    (SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S))
    ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
      p.model.coefficientPullback.iso.hom)
    ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
      (p.model.coefficientPullback.derivedIso l E).hom)
    (diagonalTrace_varying_single_square l E p hacyc
      (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)))
    (diagonalTrace_coefficient_single_adjunct l E p)

end AlgebraicGeometry.ProEtale.DiagonalTrace
