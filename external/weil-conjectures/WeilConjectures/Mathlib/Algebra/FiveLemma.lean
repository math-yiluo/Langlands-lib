/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.FiveLemma

/-!
# The four lemma for exact hexagons

Consider a commutative diagram of additive groups with exact rows
```
0 ──▶ M₁ ──▶ M₂ ──▶ M₃ ──▶ M₄ ──▶ M₅ ──▶ M₆
      │      │      │      │      │      │
      i₁     i₂     i₃     i₄     i₅     i₆
      ▼      ▼      ▼      ▼      ▼      ▼
0 ──▶ N₁ ──▶ N₂ ──▶ N₃ ──▶ N₄ ──▶ N₅ ──▶ N₆
```
If `i₂`, `i₃`, `i₅` and `i₆` are bijective, then so are `i₁` and `i₄`. This is two applications of
the four lemmas of `Mathlib.Algebra.FiveLemma`.
-/

@[expose] public section

namespace AddMonoidHom

variable {M₁ M₂ M₃ M₄ M₅ M₆ N₁ N₂ N₃ N₄ N₅ N₆ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
  [AddCommGroup M₆] [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄]
  [AddCommGroup N₅] [AddCommGroup N₆]

/-- **The four lemma for exact hexagons.** Given a commutative diagram of additive groups whose
rows `0 → M₁ → ⋯ → M₆` and `0 → N₁ → ⋯ → N₆` are exact, if the vertical maps `i₂`, `i₃`,
`i₅` and `i₆` are bijective, then so are `i₁` and `i₄`.

(blueprint: `lem-sc-four-lemma`) -/
theorem bijective_of_exact_hexagon (f₁ : M₁ →+ M₂) (f₂ : M₂ →+ M₃) (f₃ : M₃ →+ M₄)
    (f₄ : M₄ →+ M₅) (f₅ : M₅ →+ M₆) (g₁ : N₁ →+ N₂) (g₂ : N₂ →+ N₃) (g₃ : N₃ →+ N₄)
    (g₄ : N₄ →+ N₅) (g₅ : N₅ →+ N₆) (i₁ : M₁ →+ N₁) (i₂ : M₂ →+ N₂) (i₃ : M₃ →+ N₃)
    (i₄ : M₄ →+ N₄) (i₅ : M₅ →+ N₅) (i₆ : M₆ →+ N₆)
    (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
    (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
    (hc₅ : g₅.comp i₅ = i₆.comp f₅)
    (hf₀ : Function.Injective f₁) (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃)
    (hf₃ : Function.Exact f₃ f₄) (hf₄ : Function.Exact f₄ f₅)
    (hg₀ : Function.Injective g₁) (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃)
    (hg₃ : Function.Exact g₃ g₄) (hg₄ : Function.Exact g₄ g₅)
    (hi₂ : Function.Bijective i₂) (hi₃ : Function.Bijective i₃) (hi₅ : Function.Bijective i₅)
    (hi₆ : Function.Bijective i₆) :
    Function.Bijective i₁ ∧ Function.Bijective i₄ := by
  refine ⟨⟨fun a b h ↦ hf₀ (hi₂.1 ?_), ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← comp_apply, ← comp_apply, ← hc₁, comp_apply, comp_apply, h]
  · exact surjective_of_surjective_of_injective_of_left_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃ hc₁ hc₂
      hf₁ hg₁ hi₂.2 hi₃.1 hg₀
  · exact injective_of_surjective_of_injective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₂ hf₃ hg₂ hi₂.2 hi₃.1 hi₅.1
  · exact surjective_of_surjective_of_surjective_of_injective f₃ f₄ f₅ g₃ g₄ g₅ i₃ i₄ i₅ i₆
      hc₃ hc₄ hc₅ hf₄ hg₃ hg₄ hi₃.2 hi₅.2 hi₆.1

end AddMonoidHom
