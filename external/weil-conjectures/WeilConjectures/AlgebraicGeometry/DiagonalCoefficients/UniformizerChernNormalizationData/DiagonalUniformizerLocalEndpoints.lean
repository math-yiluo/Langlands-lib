/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerChernTransport

/-! # Endpoints for local uniformizer coefficient change

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

section AbstractUnit
variable {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
  {A : Type (u + 1)} [CommRing A] [Finite A]
  {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}

/-- The four unit endpoints as a composite of specified isomorphisms.
Source: coefficient changes (1).
(blueprint: def-diagonal-uniformizer-local-endpoints). -/
@[irreducible]
def ChernCoefficientDiagram.localUnitIso
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY) :
    (x.completedP.F.mapDerivedCategory ⋙ derivedScalars x.b (ProjectiveLine Y) ⋙
      derivedScalars x.q (ProjectiveLine Y) ⋙ x.eP.F.mapDerivedCategory).obj
        (DiagonalTrace.completedUnit l (ProjectiveLine Y)) ≅
      geoP1Unit A (ProjectiveLine Y) :=
  x.eP.F.mapDerivedCategory.mapIso
      ((derivedScalars x.q (ProjectiveLine Y)).mapIso
        ((derivedScalars x.b (ProjectiveLine Y)).mapIso
          ((x.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso x.completedP.unitIso) ≪≫
          (x.toIntegral.units (ProjectiveLine Y)).iso) ≪≫
        (x.scalar.units (ProjectiveLine Y)).iso) ≪≫
    (x.eP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso x.eP.unitIso ≪≫
    (finiteUnitComparison A (ProjectiveLine Y)).symm

end AbstractUnit

namespace UniformizerChernNormalizationData

/-- The four coefficient functors on P, without taking direct image.
Source: coefficient changes (1).
(blueprint: def-diagonal-uniformizer-local-endpoints). -/
@[irreducible]
def localFunctor (s : UniformizerChernNormalizationData l Y) :
    DerivedCategory (DiagonalCompleted l (ProjectiveLine Y)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y))
        (ModuleCat.{u + 1} (ULift.{u + 1} (completedResidue l s.E s.π s.n)))) :=
  s.completedP.F.mapDerivedCategory ⋙ derivedScalars (integralMap l s.E) (ProjectiveLine Y) ⋙
    derivedScalars (quotientMap l s.E s.π s.n) (ProjectiveLine Y) ⋙ s.eP.F.mapDerivedCategory

/-- The composite positive-line comparison on P, including its finite shift endpoint.
Source: coefficient changes (1), positive-root normalization.
(blueprint: def-diagonal-uniformizer-local-endpoints). -/
@[irreducible]
def localLine (s : UniformizerChernNormalizationData l Y) :
    (s.localFunctor l Y).obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) ⟶
      geoP1Twist (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (l ^ (s.n + 1)) s.hA (ProjectiveLine Y) 1 2 :=
  by
    unfold localFunctor
    exact
      s.eP.F.mapDerivedCategory.map
          ((derivedScalars (quotientMap l s.E s.π s.n) (ProjectiveLine Y)).map
            ((derivedScalars (integralMap l s.E) (ProjectiveLine Y)).map
              (s.completedP.shiftedLine l (ProjectiveLine Y)) ≫
                s.toIntegral.lineP.shift (integralMap l s.E)) ≫
            s.scalar.lineP.shift (quotientMap l s.E s.π s.n)) ≫ s.lineP.shifted l

/-- The inverse of the specified local coefficient-unit isomorphism.
Source: coefficient changes (1).
(blueprint: def-diagonal-uniformizer-local-endpoints). -/
@[irreducible]
def localUnitInv (s : UniformizerChernNormalizationData l Y) :
    geoP1Unit (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y) ⟶
      (s.localFunctor l Y).obj (DiagonalTrace.completedUnit l (ProjectiveLine Y)) := by
  unfold localFunctor
  exact ((s.diagram l Y).localUnitIso l Y).inv

/-- The positive finite Kummer equation for a local completed arrow.
Source: coefficient changes (1), reduction of the positive section class.
(blueprint: def-diagonal-uniformizer-local-endpoints). -/
@[irreducible]
def LocalChernNormalized (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) : Prop :=
  (s.localUnitInv l Y ≫ (s.localFunctor l Y).map z) ≫ s.localLine l Y =
      (geoP1Comparison (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).map
          (geoP1EtaleChern (ULift.{u + 1} (completedResidue l s.E s.π s.n))
            (l ^ (s.n + 1)) (pow_pos (Fact.out : l.Prime).pos _) s.hA Y s.hYpow)

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
