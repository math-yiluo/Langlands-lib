/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q)
    (φ : ∀ n, OModulePresheaf.AffHom (F (n + 1)) (F n))
    (hφs : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((φ n).app U))
    (hφk : ∀ (n : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ n).app U) = I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)))
    (L : ℕ → OModulePresheaf q) (hLc : ∀ n, (L n).IsCoherent) (hLq : ∀ n, (L n).IsQuasicoherent)
    (ι : ∀ n, OModulePresheaf.AffHom (L n) (F n))
    (hιi : ∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U))
    (lam : ∀ n, OModulePresheaf.AffHom (L (n + 1)) (L n))
    (hls : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U))
    (hlc : ∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (φ n).app U ∘ₗ (ι (n + 1)).app U)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      I ^ n • (⊤ : Submodule A ((F n).obj U.1)) ⊓ LinearMap.range ((ι n).app U) ≤ I ^ k • LinearMap.range ((ι n).app U)) :
    ∃ (Ks : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (Ks (k + 1)) (Ks k))
      (j : ∀ k, OModulePresheaf.AffHom (Ks k) (F k)),
      (∀ k, (Ks k).IsCoherent) ∧ (∀ k, (Ks k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.range ((ι k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
        LinearMap.ker ((j n).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ks n).obj U.1))) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution I F φ hφs hφk L hLc hLq ι hιi lam hls hlc hAR
