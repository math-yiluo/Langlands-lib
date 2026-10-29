import Langlands.Algebra.CompatibleSubmodule
import Langlands.Algebra.CompatibleUnitization
import Langlands.LinearAlgebra.StableEndomorphismStatements

/-!
# Power-chain stabilization for compatible nonunital algebra actions

Statement targets for the actual compatible kernels and ranges of powers,
formed through the published unitization correspondence. These internally
specialize Renard 2026, C.II, Lemma (iv), printed pp. 277–278 / PDF pp. 283–284.
-/

set_option autoImplicit false

namespace Langlands.Algebra.CompatiblePowerStabilization

open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Unitized powers have the expected underlying complex-linear maps. -/
def PowerUnderlyingMapStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    letI := CompatibleUnitization.module ρ
    let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
      CompatibleUnitization.toLinearIntertwiner
        ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
    ∀ n : ℕ, (powers n).toLinearMap = f.toLinearMap ^ n

/-- Actual compatible kernels increase and ranges decrease from exponent zero. -/
def PowerKernelRangeMonotonicityStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    letI := CompatibleUnitization.module ρ
    let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
      CompatibleUnitization.toLinearIntertwiner
        ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
    Monotone (fun k : ℕ => (powers k).ker) ∧
      Antitone (fun k : ℕ => (powers k).range)

/-- Under eventual stability either adjacent equality stabilizes both compatible chains. -/
def AdjacentStabilizationStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    letI := CompatibleUnitization.module ρ
    let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
      CompatibleUnitization.toLinearIntertwiner
        ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
    EventuallyStable f.toLinearMap →
    ∀ k : ℕ,
      ((powers k).ker = (powers (k + 1)).ker ↔
        (powers k).range = (powers (k + 1)).range) ∧
      (((powers k).ker = (powers (k + 1)).ker ∨
          (powers k).range = (powers (k + 1)).range) →
        ∀ m : ℕ, k ≤ m →
          (powers m).ker = (powers k).ker ∧
            (powers m).range = (powers k).range)

/-- Eventually stable compatible power chains have a common first index in `ℕ`. -/
def FirstStabilizationIndexStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    letI := CompatibleUnitization.module ρ
    let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
      CompatibleUnitization.toLinearIntertwiner
        ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
    EventuallyStable f.toLinearMap →
    ∃ k₀ : ℕ,
      (∀ m : ℕ, k₀ ≤ m →
        (powers m).ker = (powers k₀).ker ∧
          (powers m).range = (powers k₀).range) ∧
      (∀ j : ℕ, j < k₀ →
        (powers j).ker ≠ (powers (j + 1)).ker ∧
          (powers j).range ≠ (powers (j + 1)).range)

/-- The closed family of compatible-action power-chain statement targets. -/
def CompatiblePowerStabilizationStatements : Prop :=
  PowerUnderlyingMapStatement.{uB, uV} ∧
    PowerKernelRangeMonotonicityStatement.{uB, uV} ∧
    AdjacentStabilizationStatement.{uB, uV} ∧
    FirstStabilizationIndexStatement.{uB, uV}

end Langlands.Algebra.CompatiblePowerStabilization
