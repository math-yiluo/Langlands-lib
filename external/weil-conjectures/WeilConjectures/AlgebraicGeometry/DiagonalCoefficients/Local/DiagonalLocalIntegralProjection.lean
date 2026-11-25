/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerClass
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # The integral finite root projection of a completed local arrow

Source: diagonal tower coefficient changes (1), integral coefficient and root endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Forget the completed coefficient action while retaining the actual underlying sheaf.
Source: coefficient changes (1) (blueprint: def-diagonal-local-integral-projection). -/
def localCompletedForget (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    DiagonalCompleted l T ⥤ DiagonalAb T :=
  SheafOfModules.toSheaf (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))

instance (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (localCompletedForget l T).Additive := by
  dsimp [localCompletedForget]
  infer_instance

instance (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteLimits (localCompletedForget l T) := by
  dsimp [localCompletedForget]
  infer_instance

instance (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteColimits (localCompletedForget l T) :=
  (moduleSheaves_colimits_forgetful
    (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))).2.2.1

/-- The integer-cast generator of the actual completed unit.
Source: coefficient changes (1) (blueprint: def-diagonal-local-integral-projection). -/
def localCompletedGenerator (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
    (localCompletedForget l T).obj (SheafOfModules.unit
      (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))) :=
  diagonalCoefficientIntegerMap T (Scheme.purTwistZlCompletion T l)

/-- The completed line has the unchanged underlying inverse limit of roots.
Source: coefficient changes (1) (blueprint: def-diagonal-local-integral-projection). -/
def localCompletedRoots (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (localCompletedForget l T).obj (Scheme.purTwistZlModule T l) ≅
      Scheme.purTwistZlOne T l :=
  ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by ext U x; rfl, by ext U x; rfl⟩

/-- Forget a completed arrow, insert the integral generator, and project its target to
finite roots followed by the canonical scalar root map. This is a specified composite,
independent of any Chern normalization or scalar-extension realization.
Source: coefficient changes (1) (blueprint: def-diagonal-local-integral-projection). -/
@[irreducible]
def completedIntegralProjection (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (z : DiagonalTrace.completedUnit l T ⟶
      (DiagonalTrace.completedLine l T)⟦(2 : ℤ)⟧) :
    Ext.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((cartierForget A T).obj (geoCartierLine A (l ^ (n + 1)) hA T)) 2 :=
  Ext.homEquiv.symm
    ((DerivedCategory.singleFunctor _ 0).map (localCompletedGenerator l T) ≫
      SpTowerClasses.mapSingleArrow (localCompletedForget l T) 2 z ≫
      ((DerivedCategory.singleFunctor _ 0).map
        ((localCompletedRoots l T).hom ≫
          limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n) ≫
          cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hT))⟦(2 : ℤ)⟧')

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
