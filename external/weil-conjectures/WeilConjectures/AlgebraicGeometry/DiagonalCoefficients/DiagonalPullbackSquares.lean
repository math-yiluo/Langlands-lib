/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback

/-! # Separate class and trace equations for fixed pullback endpoints

Source: diagonal coefficient changes, paragraph (3), the class and trace squares.
(blueprint: def-diagonal-pullback-squares).

The small proposition wrappers keep concrete coefficient constructions out of
elaboration of the derived equation types. They contain exactly the published
fields of PullbackCompatibility and add no mathematical assumptions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
  (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L) (d' : Diagram R Y' L)
  (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
    (L (ProjectiveLine Y')).X)
  (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
    (L (diagonalSurface Y')).X)
  (s : SourcePullback R g L mP mW)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
