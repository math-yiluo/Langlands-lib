/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution X M U s hs hloc hloc₂ f
