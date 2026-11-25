/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitFiniteObjects

/-! # Named diagonal limit normalization equations

These definitions spell out the existing specification with shared endpoint and
normalization functions. No coefficient object or boundary is changed.
(blueprint: def-sfb-diagonal-limit-normalizations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The finite source normalization, with the domain of its isomorphism fixed. -/
def diagonalLimitFiniteSourceNorm (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ) (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      diagonalLimitFiniteSource ℓ Y n) : Prop :=
  DiagonalSourceNormalization ℓ Y D.ordinary n s

/-- The finite root normalization, with its target fixed by name. -/
def diagonalLimitFiniteTargetNorm (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : diagonalLimitRoots ℓ Y H) (n : ℕ)
    (t : H.obj (op n) ≅ diagonalLimitFiniteTarget ℓ Y n) : Prop :=
  HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
    (roots.hom.app (op n) ≫
      cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
        (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n))

/-- The finite equation clause of the original limit specification. -/
def diagonalLimitFiniteNormalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y)) (roots : diagonalLimitRoots ℓ Y H)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2) : Prop :=
  diagonalFiniteCycleNormalization (D.ordinary.E.obj (diagonalIntegralSource Y)) H c
    (diagonalLimitFiniteSource ℓ Y) (diagonalLimitFiniteTarget ℓ Y)
    (diagonalLimitFiniteSourceNorm ℓ Y D)
    (diagonalLimitFiniteTargetNorm ℓ Y hY H roots) (diagonalLimitFiniteClass ℓ Y hY)

/-- The ordinary limit's prescribed source generator equation. -/
def diagonalLimitSourceNorm (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    Prop :=
  ∀ n : ℕ,
    diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
      (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
      (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
        (diagonalForget ℓ (diagonalSurface Y)).map
          ((D.ordinary.π n).app (diagonalIntegralSource Y))

/-- The ordinary limit's prescribed root-tower comparison. -/
def diagonalLimitTargetNorm (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (H : DiagonalSystems ℓ (diagonalSurface Y)) (roots : diagonalLimitRoots ℓ Y H)
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) : Prop :=
  HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
    (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv

end AlgebraicGeometry.ProEtale
