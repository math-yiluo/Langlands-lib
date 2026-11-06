/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q] (𝓙 : P.IdealSheafData)
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (Q : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (Q (k + 1)) (Q k))
      (ε : ∀ k, OModulePresheaf.AffHom (F k) (Q k)),
      (∀ k, (Q k).IsCoherent) ∧ (∀ k, (Q k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Q (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ε k).app U) = OModulePresheaf.idealPowSub q 𝓙 (F k) 1 U.1) ∧
      (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q k)) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.solution I 𝓙 F hFc hFq φ hφs hφk
