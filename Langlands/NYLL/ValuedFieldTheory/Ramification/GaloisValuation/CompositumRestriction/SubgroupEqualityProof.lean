/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 242, 14 November 2026, from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709,
Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean,
M331.003 (lines 149–182). Retain the subgroup-inclusion proof; prefix the
namespace with Langlands.NYLL and prove the published closed Statement with
three explicitly independent universes. Import only the published target module.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.Statements

/-!
# Subgroup equality from two images

The exact proof of the published M331.003 subgroup equality target.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe uG uG₁ uG₂

/-- Two subgroups are equal when one jointly injective pair of homomorphisms
has equal right images and both left images are trivial. -/
theorem subgroup_eq_of_prod_map_injective_of_left_maps_eq_bot :
    subgroup_eq_of_prod_map_injective_of_left_maps_eq_botStatement.{uG, uG₁, uG₂} := by
  intro G G₁ G₂ _ _ _ f₁ f₂ hinjective A B hA₁ hB₁ h₂
  have hle (C D : Subgroup G)
      (hC₁ : C.map f₁ = ⊥) (hD₁ : D.map f₁ = ⊥)
      (hCD₂ : C.map f₂ = D.map f₂) :
      C ≤ D := by
    intro x hx
    have hfx₂ : f₂ x ∈ D.map f₂ := by
      rw [← hCD₂]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy₂⟩ := hfx₂
    have hx₁mem : f₁ x ∈ C.map f₁ := ⟨x, hx, rfl⟩
    have hy₁mem : f₁ y ∈ D.map f₁ := ⟨y, hy, rfl⟩
    rw [hC₁] at hx₁mem
    rw [hD₁] at hy₁mem
    have hx₁ : f₁ x = 1 := Subgroup.mem_bot.mp hx₁mem
    have hy₁ : f₁ y = 1 := Subgroup.mem_bot.mp hy₁mem
    have hxy : x = y := by
      apply hinjective
      apply Prod.ext
      · exact hx₁.trans hy₁.symm
      · exact hy₂.symm
    exact hxy.symm ▸ hy
  exact le_antisymm
    (hle A B hA₁ hB₁ h₂)
    (hle B A hB₁ hA₁ h₂.symm)

end Langlands.NYLL.LocalClassFieldTheory
