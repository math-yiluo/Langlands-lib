/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalEndpoints

/-! # Normalization predicates for the model Chern adjunct

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

section AbstractTransport
variable {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
  {A : Type (u + 1)} [CommRing A] [Finite A]
  {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}

/-- The prescribed four endpoint composites, with an arbitrary final arrow.
Source: coefficient changes (1), functorial transport of adjuncts.
(blueprint: def-diagonal-uniformizer-adjunct-conditions). -/
@[irreducible]
def ChernCoefficientDiagram.TransportTo
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (c : DiagonalTrace.completedUnit l Y ⟶
      x.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (w : geoP1Unit A Y ⟶
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
        (geoP1Twist A N hA (ProjectiveLine Y) 1 2)) : Prop :=
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars x.b Y
  let F₂ := derivedScalars x.q Y
  let F₃ := x.eY.F.mapDerivedCategory
  let u₀ := x.completedY.singleUnit l Y
  let u₁ := (x.toIntegral.units Y).iso.hom
  let u₂ := (x.scalar.units Y).iso.hom
  let u₃ := x.eY.derivedUnit
  let v₀ := x.q_square.derived.iso.hom.app
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) ≫
    x.zl.Rq.R.map (x.completedP.shiftedLine l (ProjectiveLine Y))
  let v₁ := (x.toIntegral.q.square.mate x.b).app _ ≫
    x.integral.Rq.R.map (x.toIntegral.lineP.shift x.b)
  let v₂ := (x.scalar.q.square.mate x.q).app _ ≫
    x.d.Rq.R.map (x.scalar.lineP.shift x.q)
  let v₃ := (x.presentation.comparison
    R
    A
    N hN hA Y hY
    x.L x.d x.eY x.eP x.lineP).hom
  fourStepChernCommutes F₀ F₁ F₂ F₃ u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ c w

end AbstractTransport

namespace UniformizerChernNormalizationData

/-- The local arrow has its prescribed whole-system root-limit normalization.
Source: trace proof (1), coefficient and root limit comparisons.
(blueprint: def-diagonal-uniformizer-adjunct-conditions). -/
@[irreducible]
def LocalNormalized (s : UniformizerChernNormalizationData l Y)
    (theta : SpTowerClasses.unit (ProjectiveLine Y)
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y)) ⟶
      (SpTowerClasses.line l (ULift.{u} (Padic l)) s.tq.chernX)⟦(2 : ℤ)⟧)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) : Prop :=
  (diagonalCompletedUnderlying l (ProjectiveLine Y)).map z ≫
        DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l (ProjectiveLine Y))
          (s.tq.restrictionX.F.mapDerivedCategory ⋙ s.tq.LX.R)
          (s.tq.coefficientsX.lineMap l (ULift.{u} (Padic l)) s.tq.LX) 2 =
      s.tq.coefficientsX.unitMap l (ULift.{u} (Padic l)) s.tq.LX ≫
        s.tq.LX.R.map (s.tq.restrictionX.F.mapDerivedCategory.map theta)

/-- The completed arrow has the prescribed canonical system-Chern normalization.
Source: trace proof (1), the actual model adjunct and its limit comparison.
(blueprint: def-diagonal-uniformizer-adjunct-conditions). -/
@[irreducible]
def AdjunctNormalized (s : UniformizerChernNormalizationData l Y)
    (c : DiagonalTrace.completedUnit l Y ⟶
      s.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)) : Prop :=
  (diagonalCompletedUnderlying l Y).map c ≫
      s.tq.toPresentation.sourceMap l (ULift.{u} (Padic l)) =
    s.tq.coefficientsS.unitMap l (ULift.{u} (Padic l)) s.tq.LS ≫
      s.tq.LS.R.map (s.tq.toPresentation.systemChern l)

end UniformizerChernNormalizationData

/-- A local positive class and its completed adjunct, with their actual normalizations.
Source: coefficient changes (1), the local class and canonical model adjunct.
(blueprint: def-diagonal-uniformizer-adjunct-conditions). -/
structure NormalizedAdjunctPair (s : UniformizerChernNormalizationData l Y) where
  z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧
  c : DiagonalTrace.completedUnit l Y ⟶
      s.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
  local_normalized : s.LocalNormalized l Y
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
      (SpTowerClasses.hyperplanePic Y)) z
  adjunct_normalized : s.AdjunctNormalized l Y c

/-- Transport of a normalized pair through the four specified coefficient comparisons.
Source: coefficient changes (1), adjunction of the local coefficient image.
(blueprint: def-diagonal-uniformizer-adjunct-conditions). -/
@[irreducible]
def NormalizedAdjunctPair.Transported
    (s : UniformizerChernNormalizationData l Y) (p : NormalizedAdjunctPair l Y s) : Prop :=
  (s.diagram l Y).TransportTo l Y p.c
      ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l s.E s.π s.n)))
          (ProjectiveLine Y ↘ Y)).homEquiv _ _
            ((geoP1UnitPullback (ULift.{u + 1} (completedResidue l s.E s.π s.n))
              (ProjectiveLine Y ↘ Y)).hom ≫
              ((s.localUnitInv l Y ≫ (s.localFunctor l Y).map p.z) ≫ s.localLine l Y)))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
