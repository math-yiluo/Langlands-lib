/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization

/-! # A single-object comparison for the varying trace square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
  Functor.mapDerivedCategorySingleFunctor Functor.rightDerivedFunctorObjQIso

/-- The varying square on any system object in degree zero.

Source: diagonal tower trace proof (1)--(2), normalized varying restriction.
(blueprint: lem-sfb-diagonal-trace-varying-single-square).

Proof: restricted-push acyclicity extends the given K-injective normalization to
all cochain complexes. Evaluate it on the given system object in degree zero.
Naturality of the cochain units and of the exact single-functor comparisons gives
precisely the displayed single-object equality. -/
theorem diagonalTrace_varying_single_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l E f)
    (hacyc : ∀ I : CochainComplex (SpTowerClasses.Systems X
      (SpTowerClasses.Arings l E X)) ℤ, I.IsKInjective →
      IsIso (p.Rt.η.app ((p.restrictionX.F.mapHomologicalComplex (.up ℤ)).obj I)))
    (M : SpTowerClasses.Systems X (SpTowerClasses.Arings l E X)) :
    let := p.base.kinjective X
    let := p.model.geometry.pushAdditive
    let := p.restrictionS.additive
    let := p.restrictionX.additive
    let := p.restrictionX.limits
    let := p.restrictionX.colimits
    let := p.restrictionS.limits
    let := p.restrictionS.colimits
    DiagonalSingleSquare p.model.geometry.push (diagonalTraceSystemPush l f)
      p.restrictionX.F p.restrictionS.F (canonicalDiagonalRightDerived p.model.geometry.push)
      p.Rt p.varyingOrdinary p.varying M := by
  let := p.base.kinjective X
  let := p.model.geometry.pushAdditive
  let := p.restrictionS.additive
  let := p.restrictionX.additive
  let := p.restrictionX.limits
  let := p.restrictionX.colimits
  let := p.restrictionS.limits
  let := p.restrictionS.colimits
  dsimp only
  exact exactSquare_single_of_kInjective p.model.geometry.push
    (diagonalTraceSystemPush l f) p.restrictionX.F p.restrictionS.F p.Rt
    p.varyingOrdinary p.varying hacyc p.varying_normalization M

end AlgebraicGeometry.ProEtale.DiagonalTrace
