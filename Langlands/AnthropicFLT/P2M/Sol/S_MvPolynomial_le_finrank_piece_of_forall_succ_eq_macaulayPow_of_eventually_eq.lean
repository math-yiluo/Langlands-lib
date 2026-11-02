/-
Ported from `P2M/Sol/S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Langlands.AnthropicFLT.Theorems.Thm_Nat_macaulayPow_lt_macaulayPow_of_lt
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzmannB29

theorem lt_of_lt {n : ℕ} {K : Type uz} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (d : ℕ) (hd : g ≤ d) (hlt : Module.finrank K (piece J d) < H d) :
    ∀ e, d ≤ e → Module.finrank K (piece J e) < H e := by
  intro e hde
  induction e with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact hlt
  | succ e ih =>
    rcases Nat.lt_or_ge e d with h | h
    · obtain rfl : d = e + 1 := by omega
      exact hlt
    · calc Module.finrank K (piece J (e + 1)) ≤ Nat.macaulayPow e (Module.finrank K (piece J e)) :=
            MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K J hJ
        _ < Nat.macaulayPow e (H e) := Nat.macaulayPow_lt_macaulayPow_of_lt (by omega) (ih h)
        _ = H (e + 1) := (hH e (by omega)).symm

theorem le_finrank_piece {n : ℕ} {K : Type uz} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (hev : ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → Module.finrank K (piece J e) = H e)
    (d : ℕ) (hd : g ≤ d) : H d ≤ Module.finrank K (piece J d) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨D₀, hD₀⟩ := hev
  have := lt_of_lt J hJ H g hg hH d hd hlt (max d D₀) (le_max_left _ _)
  rw [hD₀ _ (le_max_right _ _)] at this
  exact lt_irrefl _ this

end GotzmannB29

open GotzmannB29 in
theorem solution
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d) := by
  intro d hd
  exact GotzmannB29.le_finrank_piece J hJ H g hg hH hev d hd
