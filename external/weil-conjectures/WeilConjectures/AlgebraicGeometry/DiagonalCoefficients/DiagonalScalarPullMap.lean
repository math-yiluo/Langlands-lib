/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams

/-! # Generic scalar pullback tensor equation

Source: diagonal coefficient changes, paragraph (3).
(blueprint: def-sfb-diagonal-scalar-pull-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The balanced-tensor equation for extension of an arbitrary coefficient map.
Source: latest blueprint, diagonal coefficient changes, paragraph (3).
(blueprint: def-sfb-diagonal-scalar-pull-map). -/
def ScalarPullMap
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules R S) (N : Modules R X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (m' : (upperStar Ab.{u + 1} f).obj
      (Mod.extendScalarsObj (coefficientMap a S) M).X ⟶
        (Mod.extendScalarsObj (coefficientMap a X) N).X) : Prop :=
  (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap a S) M) ≫ m' =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj T S) M.X ≫
      (condensedPullbackHom T f ⊗ₘ m) ≫ Mod.extendπ (coefficientMap a X) N

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
