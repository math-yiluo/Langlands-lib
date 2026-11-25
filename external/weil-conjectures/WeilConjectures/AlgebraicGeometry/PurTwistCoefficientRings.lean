/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses

/-! # Coefficient rings of the integral Tate twist

Source: coefficient-twist blueprint, order 1505.
(auxiliary; not a blueprint node)

The constant and completed coefficient rings, their quotient projections, and the
canonical comparison form the coefficient data used before constructing the Tate line.
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
variable (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]

attribute [local instance] WeilConjectures.sfAbBijective

/-- Forget commutativity of a coefficient sheaf, without changing its sections.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
abbrev purTwistRingOfUniverses (R : Sheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}) :=
  (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R

/-- Constant finite coefficients at positive level `n + 1`.
Source: Stacks Tag 03PK (auxiliary; not a blueprint node). -/
noncomputable abbrev purTwistFiniteRingOfUniverses (n : ℕ) :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))))

/-- Forget commutativity of a coefficient sheaf, without changing its sections.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
abbrev purTwistRing (R : Sheaf (ProEt.topology S) CommRingCat.{t + 1}) :=
  purTwistRingOfUniverses.{t, t} S R

/-- Constant finite coefficients at positive level `n + 1`.
Source: Stacks Tag 03PK (auxiliary; not a blueprint node). -/
noncomputable abbrev purTwistFiniteRing (n : ℕ) :=
  purTwistFiniteRingOfUniverses.{t, t} S l n

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
