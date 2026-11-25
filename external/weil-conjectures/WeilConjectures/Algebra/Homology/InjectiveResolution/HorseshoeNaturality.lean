/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDegreewiseMap
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDefectFactorization
import WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLift

/-!
# Factoring maps between middle terms of short exact sequences

`CategoryTheory.ShortComplex.ShortExact.exists_factor_g_f`: a map between the middle terms of two
short exact sequences which is killed by the first map of the source and by the second map of the
target factors through the outer terms.

The steps of the horseshoe naturality argument are
`CategoryTheory.InjectiveResolution.horseshoe_degreewise_map`,
`CategoryTheory.InjectiveResolution.horseshoe_defect_factorization` and
`CategoryTheory.InjectiveResolution.corrected_middle_map`.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A map `D` from the middle of a short exact sequence `S₁` to the middle of a short exact
sequence `S₂`, killed by `S₁.f` and by `S₂.g`, factors as `S₁.g ≫ E ≫ S₂.f`. -/
lemma CategoryTheory.ShortComplex.ShortExact.exists_factor_g_f {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (D : S₁.X₂ ⟶ S₂.X₂) (hD₁ : S₁.f ≫ D = 0)
    (hD₂ : D ≫ S₂.g = 0) : ∃ E : S₁.X₃ ⟶ S₂.X₁, S₁.g ≫ E ≫ S₂.f = D := by
  have := h₁.epi_g
  have := h₂.mono_f
  refine ⟨h₂.exact.lift (h₁.exact.desc D hD₁) ?_, ?_⟩
  · rw [← cancel_epi S₁.g, h₁.exact.g_desc_assoc, hD₂, comp_zero]
  · rw [h₂.exact.lift_f, h₁.exact.g_desc]
