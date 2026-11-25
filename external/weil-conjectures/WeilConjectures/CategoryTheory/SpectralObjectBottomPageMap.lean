/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Bottom-page maps to the abutment

Source: Stacks Project, Tags 012K and 015N; spectral-object cycles model.
(blueprint: def-sc-spectral-object-bottom-page-map)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]

/-- The map from a bottom-row page to the abutment, using the cycles realization.
Source: Stacks Project, Tags 012K and 015N.
(blueprint: def-sc-spectral-object-bottom-page-map) -/
noncomputable def bottomPageMap (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
    (Y.E₂SpectralSequenceNat.page r hr).X (p, 0) ⟶
      (Y.H p).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) :=
  have := Y.isIso_H_map_twoδ₁Toδ₀' p (p + 1) rfl ⊥ (0 : ℤ) (r - 1 : ℤ)
    bot_le (WithBotTop.coe_le_coe.2 (by omega))
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
    (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
  (Y.spectralSequencePageXIso coreE₂CohomologicalNat r hr (p, 0)
    (2 - r : ℤ) (0 : ℤ) (1 : ℤ) (r - 1 : ℤ)
    (by simp; congr 1; omega) rfl (by simp) (by simp)
    (p - 1) p (p + 1) (by simp)).hom ≫
  Y.ιE (homOfLE (show ((2 - r : ℤ) : EInt) ≤ (0 : ℤ) by simp; omega))
    (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
    (homOfLE (show ((1 : ℤ) : EInt) ≤ (r - 1 : ℤ) by simp; omega))
    (p - 1) p (p + 1) ≫
  Y.fromOpcycles (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
    (homOfLE (show ((1 : ℤ) : EInt) ≤ (r - 1 : ℤ) by simp; omega))
    (homOfLE (show ((0 : ℤ) : EInt) ≤ (r - 1 : ℤ) by simp; omega))
    (Subsingleton.elim _ _) p ≫
  inv ((Y.H p).map (twoδ₁Toδ₀' (⊥ : EInt) ((0 : ℤ) : EInt) ((r - 1 : ℤ) : EInt)
    bot_le (WithBotTop.coe_le_coe.2 (by omega)))) ≫
  (Y.H p).map (twoδ₂Toδ₁' (⊥ : EInt) (r - 1 : ℤ) ⊤ bot_le le_top)

end CategoryTheory.Abelian.SpectralObject
