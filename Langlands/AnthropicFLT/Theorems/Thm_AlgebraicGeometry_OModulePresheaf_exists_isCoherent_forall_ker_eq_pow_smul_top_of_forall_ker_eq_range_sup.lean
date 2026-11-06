/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
    {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {H G : OModulePresheaf q} (hHq : H.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (h : OModulePresheaf.AffHom H G)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
    (hψs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U))
    (hψk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1)))
    (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G')
      (ψ' : ∀ k, OModulePresheaf.AffHom G' (F k)),
      G'.IsCoherent ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U ∘ₗ ρ.app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ' k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ' k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ' (k + 1)).app U = (ψ' k).app U) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution I hHq hGc hGq h F φ ψ hψs hψk hψc
