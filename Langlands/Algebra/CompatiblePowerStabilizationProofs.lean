import Langlands.Algebra.CompatiblePowerStabilizationStatements
import Langlands.LinearAlgebra.StableEndomorphismProofs

/-!
# Power-chain stabilization for actual compatible actions

The local unitized powers have the expected underlying complex-linear maps.
Faithful forgetting then transports the published complex-linear power-chain
theorems to the actual compatible kernels and ranges.
-/

set_option autoImplicit false

namespace Langlands.Algebra.CompatiblePowerStabilization

universe uB uV

/-- The locally unitized powers have the expected underlying linear maps. -/
theorem powerUnderlyingMap : PowerUnderlyingMapStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f
  dsimp only
  let _ := CompatibleUnitization.module ρ
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    ext v
    change ((CompatibleUnitization.ofLinearIntertwiner f) ^ (n + 1)) v =
      (f.toLinearMap ^ (n + 1)) v
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    exact LinearMap.congr_fun ih (f v)

/-- The actual compatible kernel and range chains are monotone and antitone. -/
theorem powerKernelRangeMonotonicity : PowerKernelRangeMonotonicityStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f
  dsimp only
  let _ := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
  have hmap : ∀ n, (powers n).toLinearMap = f.toLinearMap ^ n :=
    powerUnderlyingMap B V ρ f
  have h := Langlands.LinearAlgebra.StableEndomorphism.powerKernelRangeMonotonicity
    V f.toLinearMap
  constructor
  · intro i j hij
    have hle : (powers i).ker.toSubmodule ≤ (powers j).ker.toSubmodule := by
      simpa only [LinearIntertwiner.ker_toSubmodule, hmap] using h.1 hij
    exact CompatibleSubmodule.toSubmodule_le_toSubmodule.mp hle
  · intro i j hij
    have hle : (powers j).range.toSubmodule ≤ (powers i).range.toSubmodule := by
      simpa only [LinearIntertwiner.range_toSubmodule, hmap] using h.2 hij
    exact CompatibleSubmodule.toSubmodule_le_toSubmodule.mp hle

/-- Under eventual stability, either adjacent equality stabilizes both chains. -/
theorem adjacentStabilization : AdjacentStabilizationStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f
  dsimp only
  let _ := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
  have hmap : ∀ n, (powers n).toLinearMap = f.toLinearMap ^ n :=
    powerUnderlyingMap B V ρ f
  have hker (i j : ℕ) :
      (powers i).ker = (powers j).ker ↔
        LinearMap.ker (f.toLinearMap ^ i) = LinearMap.ker (f.toLinearMap ^ j) := by
    rw [← CompatibleSubmodule.toSubmodule_inj,
      LinearIntertwiner.ker_toSubmodule, LinearIntertwiner.ker_toSubmodule, hmap, hmap]
  have hrange (i j : ℕ) :
      (powers i).range = (powers j).range ↔
        LinearMap.range (f.toLinearMap ^ i) = LinearMap.range (f.toLinearMap ^ j) := by
    rw [← CompatibleSubmodule.toSubmodule_inj,
      LinearIntertwiner.range_toSubmodule, LinearIntertwiner.range_toSubmodule, hmap, hmap]
  intro h k
  simpa only [← hker, ← hrange] using
    Langlands.LinearAlgebra.StableEndomorphism.adjacentStabilization V f.toLinearMap h k

/-- Both actual compatible chains have the same first stabilization index. -/
theorem firstStabilizationIndex : FirstStabilizationIndexStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f
  dsimp only
  let _ := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
  have hmap : ∀ n, (powers n).toLinearMap = f.toLinearMap ^ n :=
    powerUnderlyingMap B V ρ f
  have hker (i j : ℕ) :
      (powers i).ker = (powers j).ker ↔
        LinearMap.ker (f.toLinearMap ^ i) = LinearMap.ker (f.toLinearMap ^ j) := by
    rw [← CompatibleSubmodule.toSubmodule_inj,
      LinearIntertwiner.ker_toSubmodule, LinearIntertwiner.ker_toSubmodule, hmap, hmap]
  have hrange (i j : ℕ) :
      (powers i).range = (powers j).range ↔
        LinearMap.range (f.toLinearMap ^ i) = LinearMap.range (f.toLinearMap ^ j) := by
    rw [← CompatibleSubmodule.toSubmodule_inj,
      LinearIntertwiner.range_toSubmodule, LinearIntertwiner.range_toSubmodule, hmap, hmap]
  intro h
  simpa only [ne_eq, ← hker, ← hrange] using
    Langlands.LinearAlgebra.StableEndomorphism.firstStabilizationIndex V f.toLinearMap h

/-- The exact closed compatible-action power-chain aggregate. -/
theorem compatiblePowerStabilization : CompatiblePowerStabilizationStatements.{uB, uV} :=
  ⟨powerUnderlyingMap, powerKernelRangeMonotonicity,
    adjacentStabilization, firstStabilizationIndex⟩

end Langlands.Algebra.CompatiblePowerStabilization
