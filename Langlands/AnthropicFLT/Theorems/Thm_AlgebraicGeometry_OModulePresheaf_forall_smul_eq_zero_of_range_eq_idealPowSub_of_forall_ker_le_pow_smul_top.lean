/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (S : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (S (k + 1)) (S k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((S (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (S k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (𝓙 𝓙₁ 𝓙₂ : P.IdealSheafData) (s t : ℕ)
    (hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙₁ (S k) 1 U.1)
    (hji : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)))
    (hle : ∀ U : P.affineOpens, 𝓙₂.ideal U ^ t * 𝓙₁.ideal U ≤ 𝓙.ideal U ^ s)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ s, ∀ x : (S k).obj U.1, a • x = 0) :
    ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙₂.ideal U ^ t, ∀ y : (K k).obj U.1, a • y = 0 :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.solution I S φ hφs hφk K κ hκs hκk j hjc 𝓙 𝓙₁ 𝓙₂ s t hjr hji hle hS
