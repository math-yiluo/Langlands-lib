/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-! # Normalized diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-category).

## Main definitions

- `Modules`, `unit`, `source`: the coefficient category and fixed endpoints.
- `Diagram`: the diagonal class, normalized traces and integration equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b v v' w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A model of right derivation is identified with the canonical functor
through its full unit on complexes. Merely equating the functors would allow
rescaling the universal unit and hence a trace. Source: blueprint canonical
trace and coefficient/direct-image normalizations
(blueprint: def-sfb-diagonal-coefficient-category). -/
def IsCanonicalRightDerived
    {C : Type a} [Category.{v} C] [Abelian C]
    {D : Type b} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (R : DiagonalRightDerived F)
    (e : R.R = F.rightDerivedFunctor) : Prop :=
  ∀ K : CochainComplex C ℤ,
    R.η.app K ≫ (eqToIso e).hom.app (DerivedCategory.Q.obj K) = F.rightDerivedFunctorUnitQ K

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Modules over the specified pulled-back condensed coefficient, without changing
its site or coefficient universe. Source: blueprint diagonal coefficient changes
(blueprint: def-sfb-diagonal-coefficient-category). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The coefficient unit in degree zero. Source: blueprint coefficient changes
(blueprint: def-sfb-diagonal-coefficient-category). -/
abbrev unit (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (Modules Λ X) 0).obj (Mod.regular (condensedRingObj Λ X))

/-- The actual supported coefficient source of the diagonal class. Source: blueprint
coefficient changes (blueprint: def-sfb-diagonal-coefficient-category). -/
abbrev source (Y : Scheme.{u}) :=
  (CondensedRing.lowerStar Λ (diagonalImmersion Y)).obj
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))

/-- The canonical supported-source normalization, on underlying sheaves. Source:
blueprint coefficient changes, integration identities
(blueprint: def-sfb-diagonal-coefficient-category). -/
def SupportNormalization (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (i : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ≅
      (CondensedRing.lowerStar Λ f).obj (source Λ Y))
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) : Prop :=
  HEq i.inv.hom
    (((ProEtale.lowerStarComp Ab.{u + 1} (diagonalImmersion Y) f) ≪≫
      ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
      ProEtale.lowerStarId Ab.{u + 1} (ProjectiveLine Y)).hom.app
        (condensedRingObj Λ (ProjectiveLine Y)))

/-- A diagonal class and the three projective-line traces, including the two
normalized integration identities. The right derived functors retain their universal
units and K-injective computation; the supported-source maps are fixed by composition,
not chosen arbitrary arrows. Source: blueprint coefficient changes, clauses 1--3
(blueprint: def-sfb-diagonal-coefficient-category). -/
structure Diagram (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) where
  Rq : DiagonalRightDerived (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y))
  R₁ : DiagonalRightDerived (CondensedRing.lowerStar Λ
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
  R₂ : DiagonalRightDerived (CondensedRing.lowerStar Λ
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
  q_canonical : Rq.R = (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)).rightDerivedFunctor
  p₁_canonical : R₁.R = (CondensedRing.lowerStar Λ
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).rightDerivedFunctor
  p₂_canonical : R₂.R = (CondensedRing.lowerStar Λ
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).rightDerivedFunctor
  q_unit : IsCanonicalRightDerived
    (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)) Rq q_canonical
  p₁_unit : IsCanonicalRightDerived (CondensedRing.lowerStar Λ
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))) R₁ p₁_canonical
  p₂_unit : IsCanonicalRightDerived (CondensedRing.lowerStar Λ
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))) R₂ p₂_canonical
  delta : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶
    ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧
  traceq : Rq.R.obj
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y)))⟦(2 : ℤ)⟧) ⟶ unit Λ Y
  trace₁ : R₁.R.obj
    (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧) ⟶ unit Λ (ProjectiveLine Y)
  trace₂ : R₂.R.obj
    (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧) ⟶ unit Λ (ProjectiveLine Y)
  support₁ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar Λ
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))) R₁
    (source Λ Y) (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization Λ Y _)
  support₂ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar Λ
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))) R₂
    (source Λ Y) (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization Λ Y _)
  integration₁ : support₁.hom ≫ R₁.R.map delta ≫ trace₁ = 𝟙 _
  integration₂ : support₂.hom ≫ R₂.R.map delta ≫ trace₂ = 𝟙 _

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
