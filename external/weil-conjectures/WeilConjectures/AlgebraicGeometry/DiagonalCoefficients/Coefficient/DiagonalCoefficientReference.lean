/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams

/-! # Whole-system completed reference for diagonal coefficients

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-reference).

## Main definitions

- `CompletedRealization`: the exact coefficient realization with fixed endpoints.
- `Reference`: the whole completed class and trace comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- An exact realization of completed modules as modules over the actual
condensed Z_l coefficient, retaining its underlying-sheaf comparison. All
subsequent normalizations refer to this comparison, rather than to an unnamed
equivalence. Source: blueprint coefficient changes, clause 1
(blueprint: def-sfb-diagonal-coefficient-reference). -/
structure CompletedRealization (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  F : DiagonalCompleted l X ⥤ Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X
  [additive : F.Additive]
  [limits : PreservesFiniteLimits F]
  [colimits : PreservesFiniteColimits F]
  [equivalence : F.IsEquivalence]
  underlying : F ⋙ Mod.forget _ ≅ diagonalCompletedRestriction l X ⋙ diagonalForget l X
  unitIso : F.obj (SheafOfModules.unit
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≅
    Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
  unit_normalization : ∀ n : ℕ,
    HEq (underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≫
        unitIso.hom.hom ≫ (purZlReduction l X (n + 1)).hom)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (Scheme.purTwistZlProjection X l n)) ≫
        (sfbConstantRingAbIso X
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom)
  lineIso : F.obj (Scheme.purTwistZlModule X l) ≅ zlLine l X
  roots : IntegralRoots l (bottomField l) X
  line_normalization :
    HEq (underlying.inv.app (Scheme.purTwistZlModule X l) ≫ lineIso.hom.hom) roots.hom

attribute [instance] CompletedRealization.additive CompletedRealization.limits
  CompletedRealization.colimits CompletedRealization.equivalence

/-- A realization/direct-image square, normalized on underlying sheaves and by
the full derived universal unit. The independent localization universes are
retained. Source: blueprint clause 1, coefficient/direct-image comparison
(blueprint: def-sfb-diagonal-coefficient-reference). -/
structure CompletedPushSquare (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (R' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)) where
  ordinary : diagonalTracePush l f ⋙ eS.F ≅
    eX.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  ordinary_normalization : ∀ M : DiagonalCompleted l X,
    HEq ((ordinary.hom.app M).hom ≫
        (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
      (eS.underlying.hom.app ((diagonalTracePush l f).obj M))
  derived : DiagonalTrace.ExactSquareOfUniverses (diagonalTracePush l f)
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    eX.F eS.F R R' ordinary

/-- The line realization, with canonical single and shift comparisons.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-reference). -/
def CompletedRealization.shiftedLine (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    e.F.mapDerivedCategory.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
          (zlLine l X))⟦(2 : ℤ)⟧ :=
  (e.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    ((e.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule X l))⟦(2 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).map e.lineIso.hom)⟦(2 : ℤ)⟧'

/-- The coefficient-unit realization in degree zero.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-reference). -/
def CompletedRealization.singleUnit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    e.F.mapDerivedCategory.obj (DiagonalTrace.completedUnit l X) ⟶
      unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
  (e.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).map e.unitIso.hom

/-- Compatibility of one completed trace with its condensed Z_l realization.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-reference). -/
def CompletedTraceCompatibility (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (square : CompletedPushSquare l f eX eS t.Rc R)
    (trace : R.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) : Prop :=
  eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S =
    square.derived.iso.hom.app _ ≫ R.R.map (eX.shiftedLine l X) ≫ trace

/-- The initial member of the coefficient family is the recorded whole-system
limit class and the recorded completed traces, with source and root
normalizations. It cannot be an unrelated class satisfying only its finite
components. Source: blueprint clauses 1--2
(blueprint: def-sfb-diagonal-coefficient-reference). -/
structure Reference (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) where
  eY : CompletedRealization l Y
  eP : CompletedRealization l (ProjectiveLine Y)
  eW : CompletedRealization l (diagonalSurface Y)
  sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
    source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y
  source_normalization :
    HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ sourceIso.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom))
  delta :
    (DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).map
        sourceIso.inv ≫ SpTowerClasses.mapSingleArrow eW.F (2 : ℤ) δ ≫
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).map
          eW.lineIso.hom)⟦(2 : ℤ)⟧' = family.zl.delta
  tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y)
  t₁ : DiagonalTrace.Result l (ULift.{u} (Padic l))
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  t₂ : DiagonalTrace.Result l (ULift.{u} (Padic l))
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  q_model : tq.model.model = Iso.refl (ProjectiveLine Y)
  p₁_model : t₁.model.model = diagonalTraceFirstModel Y
  p₂_model : t₂.model.model = diagonalTraceSecondModel Y
  q_square : CompletedPushSquare l (ProjectiveLine Y ↘ Y) eP eY tq.Rc family.zl.Rq
  p₁_square : CompletedPushSquare l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP t₁.Rc family.zl.R₁
  p₂_square : CompletedPushSquare l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP t₂.Rc family.zl.R₂
  q_trace : CompletedTraceCompatibility l (ProjectiveLine Y ↘ Y)
    eP eY tq family.zl.Rq q_square family.zl.traceq
  p₁_trace : CompletedTraceCompatibility l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    eW eP t₁ family.zl.R₁ p₁_square family.zl.trace₁
  p₂_trace : CompletedTraceCompatibility l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    eW eP t₂ family.zl.R₂ p₂_square family.zl.trace₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
