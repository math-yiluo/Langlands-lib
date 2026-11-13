/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted M144.044, M144.045 and
M144.049; prefixed the namespace with Langlands.NYLL and reduced imports.
The source data bodies, internal proof terms and parameter binding are unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.NumberTheory.LocalField.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.Definitions

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The inclusion `𝒪_L -> L` as an `𝒪_K`-linear map, using the valuation-extension
map `𝒪_K -> 𝒪_L` for the scalar action. -/
def integerRingToFieldLinearMap : 𝒪[L] →ₗ[𝒪[K]] L where
  toFun x := (x : L)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

/-- The valuation integer ring of `L`, viewed as an `𝒪_K`-submodule of `L`.
This is the `𝒪_L` lattice compared with the normal-basis lattice. -/
def integerRingFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | x ∈ 𝒪[L]}
  zero_mem' := by
    change (0 : L) ∈ 𝒪[L]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    change x + y ∈ 𝒪[L]
    exact add_mem hx hy
  smul_mem' := by
    intro a x hx
    change a • x ∈ 𝒪[L]
    rw [Algebra.smul_def]
    have ha : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
      change algebraMap K L (a : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L a).2
    exact mul_mem ha hx

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The maximal ideal `𝓂_L`, viewed inside `L` as an `𝒪_K`-submodule. -/
def maximalIdealFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x}
  zero_mem' := by
    exact ⟨0, (𝓂[L] : Ideal 𝒪[L]).zero_mem,
      ZeroMemClass.coe_zero (ValuativeRel.valuation L).integer⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact ⟨a + b, (𝓂[L] : Ideal 𝒪[L]).add_mem ha hb, rfl⟩
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨integerRingMapOfValuationExtension K L c * a, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ (integerRingMapOfValuationExtension K L c) ha
    · change ((integerRingMapOfValuationExtension K L c : 𝒪[L]) : L) * (a : L) =
        c • (a : L)
      rw [Algebra.smul_def]
      congr 1

end
end Langlands.NYLL.CyclicCohomology
