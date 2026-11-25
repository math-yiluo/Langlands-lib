/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

/-! # Normalized coefficient cones for the trace
Source: blueprint main-20261015, sk-prop-diagonal-tower-trace, proof steps 1--8
(blueprint: def-sfb-diagonal-trace-coefficients).

## Main definitions
- `DiagonalTrace.completedUnit` and `DiagonalTrace.completedLine` are degree-zero objects.
- `DiagonalTrace.Coefficients` fixes the finite coefficient and root cones.
- `DiagonalTrace.Coefficients.unitMap` and `.lineMap` are their derived-limit maps.
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

/-- The completed unit in degree zero, with its actual coefficient-sheaf action.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-coefficients). -/
abbrev completedUnit (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] :=
  (DerivedCategory.singleFunctor (DiagonalCompleted l T) 0).obj
    (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l)))

/-- The completed root-limit Tate line in degree zero.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-coefficients). -/
abbrev completedLine (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] :=
  (DerivedCategory.singleFunctor (DiagonalCompleted l T) 0).obj (Scheme.purTwistZlModule T l)

/-- The two canonical coefficient cones. All comparisons are normalized on sections:
coefficient one goes to one, a root goes to its tensor with one, and the completed
projections are the actual ring-limit and root-limit projections.
Source: blueprint trace proof steps 4--5
(blueprint: def-sfb-diagonal-trace-coefficients). -/
structure Coefficients (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (c : Chern l E T) (r : Restriction l E T) where
  coefficientForget :
    r.F.obj (coefficient T (Arings l E T)) ⋙ diagonalForget l T ≅
      Scheme.purTwistZlTower T l ⋙
        sheafCompose (Scheme.ProEt.topology T)
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
            forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  coefficient_one : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((r.F.obj (coefficient T (Arings l E T))).obj (op n)).obj.obj U),
    HEq x (1 : (SpTowerClasses.systemRing l E T).obj.obj (op (n, U.unop))) →
      (coefficientForget.hom.app (op n)).hom.app U x =
        (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U)
  lineForget : r.F.obj (lineModule l E c) ⋙ diagonalForget l T ≅ roots l T
  line_tensor : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : c.rootModule.val.obj (op (n, U.unop)))
      (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
      (v : ((r.F.obj (lineModule l E c)).obj (op n)).obj.obj U),
    HEq x x' →
    HEq v (SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
      (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) →
      (lineForget.hom.app (op n)).hom.app U v =
        (c.rootForget.hom.app (op n)).hom.app U x'
  coefficientProjection :
    (Functor.const ℕᵒᵖ).obj ((diagonalCompletedRestriction l T).obj
      (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l)))) ⟶
        r.F.obj (coefficient T (Arings l E T))
  coefficient_projection : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((diagonalCompletedRestriction l T).obj
        (SheafOfModules.unit (Scheme.purTwistRing T
          (Scheme.purTwistZlCompletion T l)))).obj.obj U),
    (coefficientForget.hom.app (op n)).hom.app U
        ((coefficientProjection.app (op n)).hom.app U x) =
      (Scheme.purTwistZlProjection T l n).hom.app U x
  lineProjection :
    (Functor.const ℕᵒᵖ).obj ((diagonalCompletedRestriction l T).obj
      (Scheme.purTwistZlModule T l)) ⟶ r.F.obj (lineModule l E c)
  line_projection : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((diagonalCompletedRestriction l T).obj
        (Scheme.purTwistZlModule T l)).obj.obj U),
    (lineForget.hom.app (op n)).hom.app U
        ((lineProjection.app (op n)).hom.app U x) =
      (limit.π (roots l T) (op n)).hom.app U x

end AlgebraicGeometry.ProEtale.DiagonalTrace
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures
/-- The completed coefficient cone mapped through the universal derived-limit unit.
Source: blueprint trace proof step 5 (blueprint: def-sfb-diagonal-trace-coefficients). -/
def Coefficients.unitMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) (L : DiagonalRlim (DiagonalMod l T)) :
    (diagonalCompletedUnderlying l T).obj (completedUnit l T) ⟶
      L.R.obj (r.F.mapDerivedCategory.obj (unit T (Arings l E T))) :=
  exactConeComparison (diagonalCompletedRestriction l T) r.F L _ _ a.coefficientProjection

/-- The analogous root-limit comparison, prior to the shift by two.
Source: blueprint trace proof step 5 (blueprint: def-sfb-diagonal-trace-coefficients). -/
def Coefficients.lineMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) (L : DiagonalRlim (DiagonalMod l T)) :
    (diagonalCompletedUnderlying l T).obj (completedLine l T) ⟶
      L.R.obj (r.F.mapDerivedCategory.obj (line l E c)) :=
  exactConeComparison (diagonalCompletedRestriction l T) r.F L _ _ a.lineProjection

end AlgebraicGeometry.ProEtale.DiagonalTrace
