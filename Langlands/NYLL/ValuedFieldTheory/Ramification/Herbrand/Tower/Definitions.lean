/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 542 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709, Herbrand/Tower.lean,
lines 44–55, 73–74 and 141–150. Changes: namespace isolation, focused
Mathlib imports, and reuse of MonoidHom.fiberEquivKer for the equivalence.
See the paired Markdown and licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.WithBot

/-!
# Nonarchimedean depth and quotient fibres

The depth structure records four intrinsic group laws. The actual quotient
fibres and their equivalences with the normal subgroup are independent of
the depth structure. All three constructions apply to arbitrary groups.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory

/-- The purely group-theoretic laws of discrete nonarchimedean depth. -/
structure NonarchimedeanDepth (G : Type u) [Group G] where
  /-- The discrete depth of each group element. -/
  depth : G → WithTop ℕ
  /-- Infinite depth occurs exactly at the identity. -/
  depth_eq_top_iff : ∀ σ, depth σ = ⊤ ↔ σ = 1
  /-- Multiplication does not decrease the minimum depth. -/
  depth_mul_ge_min : ∀ σ τ, min (depth σ) (depth τ) ≤ depth (σ * τ)
  /-- Unequal depths give a product of depth equal to their minimum. -/
  depth_mul_eq_min_of_ne :
    ∀ {σ τ}, depth σ ≠ depth τ → depth (σ * τ) = min (depth σ) (depth τ)
  /-- Depth is invariant under conjugation. -/
  depth_conj : ∀ γ σ, depth (γ * σ * γ⁻¹) = depth σ

namespace NonarchimedeanDepth

variable {G : Type u} [Group G] (H : Subgroup G) [H.Normal]

/-- The actual fibre of the canonical quotient homomorphism over `q`. -/
abbrev QuotientFiber (q : G ⧸ H) : Type u :=
  {σ : G // QuotientGroup.mk' H σ = q}

/-- Multiplication by `σ` identifies `H` with the fibre over the class of `σ`.
The inverse sends `γ` to `σ⁻¹ * γ`. -/
def rightCosetEquivQuotientFiber (σ : G) :
    H ≃ QuotientFiber H (QuotientGroup.mk' H σ) :=
  (Equiv.subtypeEquivRight
    (p := fun τ : G => τ ∈ H)
    (q := fun τ : G => τ ∈ (QuotientGroup.mk' H).ker)
    (fun τ => (QuotientGroup.eq_one_iff (N := H) (x := τ)).symm)).trans
      ((QuotientGroup.mk' H).fiberEquivKer σ).symm

end NonarchimedeanDepth

end Langlands.NYLL.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory
