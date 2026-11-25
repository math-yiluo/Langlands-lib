/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients

/-! # The normalized trace construction
Source: blueprint main-20261015, sk-prop-diagonal-tower-trace, proof steps 1--8
(blueprint: def-sfb-diagonal-trace-presentation).

## Main definitions
- `DiagonalTrace.Presentation` fixes the geometric and coefficient comparisons.
- `DiagonalTrace.Presentation.splitting` and `.systemTrace` are strict-system morphisms.
- `DiagonalTrace.Presentation.IsTrace` fixes the completed trace by its whole-system limit.
- `DiagonalTrace.Result` records the splitting, completed trace and finite reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u w v a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses WeilConjectures

section Presentation

-- The fixed-coefficient zero morphisms differ from those of the abelian structure used by
-- `DerivedCategory.Q`; unifying the two unfolds both abelian structures in the kernel.
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms

/-- A presentation of the canonical trace construction. These are specified derived
functors and normalized comparisons, not arbitrary arrows with specified level values.
Source: blueprint trace proof steps 1--8
(blueprint: def-sfb-diagonal-trace-presentation). -/
structure Presentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (f : X ⟶ S) [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] where
  base : SpTowerShriek.Base l E
  chernS : Chern l E S
  chernX : Chern l E X
  normalizedS : chernS.Normalized l E
  normalizedX : chernX.Normalized l E
  finiteS : FiniteChernNormalization l E chernS
  finiteX : FiniteChernNormalization l E chernX
  twistS : Twisting l E chernS
  twistX : Twisting l E chernX
  model : Model l E base S X f chernS chernX twistS twistX
  restrictionS : Restriction l E S
  restrictionX : Restriction l E X
  coefficientsS : Coefficients l E S chernS restrictionS
  coefficientsX : Coefficients l E X chernX restrictionX
  LS : DiagonalRlim (DiagonalMod l S)
  LX : DiagonalRlim (DiagonalMod l X)
  Rf : DiagonalRightDerived
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
  Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)
  Rc : DiagonalRightDerived (diagonalTracePush l f)
  varyingOrdinary : model.geometry.push ⋙ restrictionS.F ≅
    restrictionX.F ⋙ diagonalTraceSystemPush l f
  varying_sections : ∀ (M : Systems X (Arings l E X)) (n : ℕ) (U : S.ProEtᵒᵖ)
      (x : (((model.geometry.push ⋙ restrictionS.F).obj M).obj (op n)).obj.obj U),
    HEq (((varyingOrdinary.hom.app M).app (op n)).hom.app U x) x
  varying : SpTowerShriek.push l E base model.geometry ⋙
      restrictionS.F.mapDerivedCategory ≅ restrictionX.F.mapDerivedCategory ⋙ Rt.R
  varying_normalization : ∀ (P : CochainComplex (Systems X (Arings l E X)) ℤ)
      (hP : P.IsKInjective),
    letI := hP
    letI : model.geometry.push.Additive := model.geometry.pushAdditive
    letI : restrictionS.F.Additive := restrictionS.additive
    letI : restrictionX.F.Additive := restrictionX.additive
    letI : (model.geometry.push ⋙ restrictionS.F).Additive := inferInstance
    letI : (restrictionX.F ⋙ diagonalTraceSystemPush l f).Additive := inferInstance
    varying.hom.app (DerivedCategory.Q.obj P) ≫
        Rt.R.map (restrictionX.F.mapDerivedCategoryFactors.hom.app P) =
      restrictionS.F.mapDerivedCategory.map
          ((model.geometry.push.rightDerivedFunctorObjQIso P).hom) ≫
        restrictionS.F.mapDerivedCategoryFactors.hom.app
          ((model.geometry.push.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex varyingOrdinary.hom (.up ℤ)).app P) ≫
        Rt.η.app ((restrictionX.F.mapHomologicalComplex (.up ℤ)).obj P)
  completedOrdinary : diagonalTracePush l f ⋙ diagonalCompletedRestriction l S ≅
    diagonalCompletedRestriction l X ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  completed_sections : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
      (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U),
    HEq ((completedOrdinary.hom.app M).hom.app U x) x
  completed : ExactSquare (diagonalTracePush l f)
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
    Rc Rf completedOrdinary
  limits : LimitSquare l f LX LS Rf Rt
  unit_limit : IsIso (coefficientsS.unitMap l E LS)
  line_limit : IsIso (coefficientsX.lineMap l E LX)

end Presentation

/-- The unit-plus-section splitting, as a morphism of strict constant-coefficient
systems. The biproduct comparison is the canonical one for the exact restriction.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-presentation). -/
def Presentation.splitting (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} {f : X ⟶ S} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] (p : Presentation l E f) :
    p.restrictionS.F.mapDerivedCategory.obj (unit S (Arings l E S)) ⊞
        p.restrictionS.F.mapDerivedCategory.obj
          ((inverseLine l E p.chernS)⟦(-2 : ℤ)⟧) ⟶
      p.Rt.R.obj (p.restrictionX.F.mapDerivedCategory.obj (unit X (Arings l E X))) :=
  biprod.desc
      (p.restrictionS.F.mapDerivedCategory.map (unitArrow l E p.model.coefficientPullback))
      (p.restrictionS.F.mapDerivedCategory.map (p.model.second l E)) ≫
    p.varying.hom.app _

/-- Twist the specified splitting, take its inverse and second projection, and
restrict scalars. This is one strict-system morphism before applying any limit.
Source: blueprint trace clause 1 and proof step 4
(blueprint: def-sfb-diagonal-trace-presentation). -/
def Presentation.systemTrace (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} {f : X ⟶ S} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] (p : Presentation l E f) [IsIso (p.model.bq l E)] :
    p.Rt.R.obj (p.restrictionX.F.mapDerivedCategory.obj
      ((line l E p.chernX)⟦(2 : ℤ)⟧)) ⟶
        p.restrictionS.F.mapDerivedCategory.obj (unit S (Arings l E S)) :=
  p.varying.inv.app _ ≫ p.restrictionS.F.mapDerivedCategory.map (p.model.trace l E)

/-- The limit of the specified strict-system trace, with its source comparison
normalized by the completed direct-image unit and its coefficient cones.
Source: blueprint trace proof steps 5--7
(blueprint: def-sfb-diagonal-trace-presentation). -/
def Presentation.IsTrace (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} {f : X ⟶ S} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] (p : Presentation l E f) [IsIso (p.model.bq l E)]
    (t : p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧) ⟶ completedUnit l S) : Prop :=
  (diagonalCompletedUnderlying l S).map t ≫ p.coefficientsS.unitMap l E p.LS =
    p.completed.iso.hom.app _ ≫
      p.Rf.R.map
        (shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l E p.LX) 2) ≫
      p.limits.iso.hom.app _ ≫ p.LS.R.map (p.systemTrace l E)

end AlgebraicGeometry.ProEtale.DiagonalTrace

namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses WeilConjectures

/-- The unit component of the twisted splitting, using the specified line pullback.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-presentation). -/
def Model.twistedUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cX : Chern l E X}
    {tS : Twisting l E cS} {tX : Twisting l E cX}
    (m : Model l E b S X f cS cX tS tX) :
    (line l E cS)⟦(2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b m.geometry).obj ((line l E cX)⟦(2 : ℤ)⟧) :=
  (SpTowerShriek.adjunction l E b m.geometry).unit.app _ ≫
    (SpTowerShriek.push l E b m.geometry).map
      (((SpTowerShriek.pull l E b m.geometry).commShiftIso (2 : ℤ)).hom.app _ ≫
        ((m.linePullback.derivedIso l E).hom)⟦(2 : ℤ)⟧')

/-- The canonical source comparison before taking the limit of the system trace.
Source: blueprint trace proof steps 5--7
(blueprint: def-sfb-diagonal-trace-presentation). -/
def Presentation.sourceMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} {f : X ⟶ S} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] (p : Presentation l E f) :
    (diagonalCompletedUnderlying l S).obj
        (p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧)) ⟶
      p.LS.R.obj (p.Rt.R.obj (p.restrictionX.F.mapDerivedCategory.obj
        ((line l E p.chernX)⟦(2 : ℤ)⟧))) :=
  p.completed.iso.hom.app _ ≫
    p.Rf.R.map
      (shiftedComparison (diagonalCompletedUnderlying l X)
        (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
        (p.coefficientsX.lineMap l E p.LX) 2) ≫ p.limits.iso.hom.app _

/-- The splitting, its completed trace, and the actual projection equations expressing
finite reduction. The evaluated trace is normalized by the torsion unit/Chern splitting.
Source: blueprint trace clause 1 and proof steps 3--8
(blueprint: def-sfb-diagonal-trace-presentation). -/
structure Result (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (f : X ⟶ S) [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] extends Presentation l E f where
  [split : IsIso (model.bq l E)]
  strict_split : IsIso (toPresentation.splitting l E)
  trace : Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧) ⟶ completedUnit l S
  construction : toPresentation.IsTrace l E trace
  reductions : ∀ n : ℕ,
    (diagonalCompletedUnderlying l S).map trace ≫ coefficientsS.unitMap l E LS ≫
        (LS.projection n).app
          (restrictionS.F.mapDerivedCategory.obj (unit S (Arings l E S))) =
      toPresentation.sourceMap l E ≫ (LS.projection n).app
          (Rt.R.obj (restrictionX.F.mapDerivedCategory.obj
            ((line l E chernX)⟦(2 : ℤ)⟧))) ≫
        ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory.map
          (toPresentation.systemTrace l E)
  torsion_unit : ∀ n : ℕ,
    (SpTowerShriek.Ev l E S n).map (model.twistedUnit l E ≫ model.trace l E) = 0
  torsion_chern : ∀ n : ℕ,
    (SpTowerShriek.Ev l E S n).map (model.chernAdjoint l E ≫ model.trace l E) =
      𝟙 ((SpTowerShriek.Ev l E S n).obj (unit S (Arings l E S)))

attribute [instance] Result.split

end AlgebraicGeometry.ProEtale.DiagonalTrace
