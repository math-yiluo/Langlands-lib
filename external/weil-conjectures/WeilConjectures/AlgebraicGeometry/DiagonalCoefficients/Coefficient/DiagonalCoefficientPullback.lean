/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback

/-! # Canonical pullback of diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-pullback).

## Main definitions

- `PullbackCompatibility`: the diagonal and three trace squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Pullback compatibility of the diagonal and all three traces, including the
canonical supported-source mate. The only asserted base-change isomorphisms are
on these specified coefficient objects. Source: blueprint clause 3 and proof
steps 3a--3c (blueprint: def-sfb-diagonal-coefficient-pullback). -/
structure PullbackCompatibility
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (d' : Diagram R Y' L)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) where
  sourceData : SourcePullback R g L mP mW
  delta :
    (derivedUpper R (baseW g)).map d.delta ≫ sourceData.endpoints.lineW.shift =
      (singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          sourceData.supported.hom ≫ d'.delta
  traceq : TracePullback R (ProjectiveLine Y ↘ Y) (ProjectiveLine Y' ↘ Y')
    (baseP g) g (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    d.Rq d'.Rq d.q_canonical d'.q_canonical
    sourceData.endpoints.lineP sourceData.endpoints.cY d.traceq d'.traceq
  trace₁ : TracePullback R
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (baseW g) (baseP g) sourceData.geometry.first_square d.R₁ d'.R₁ d.p₁_canonical d'.p₁_canonical
    sourceData.endpoints.lineW sourceData.endpoints.cP d.trace₁ d'.trace₁
  trace₂ : TracePullback R
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (baseW g) (baseP g) sourceData.geometry.second_square d.R₂ d'.R₂ d.p₂_canonical d'.p₂_canonical
    sourceData.endpoints.lineW sourceData.endpoints.cP d.trace₂ d'.trace₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
