/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
    {A : Type u} [CommRing A] (I : Ideal A)
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
      (η : ∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → ((F k).obj U.1 →ₗ[A] (F' k).obj V.1)),
      (∀ k, (F' k).IsCoherent) ∧ (∀ k, (F' k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((φ' k).app V)) ∧
      (∀ (k : ℕ) (V : V'.affineOpens),
        LinearMap.ker ((φ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A ((F' (k + 1)).obj V.1))) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : (F k).obj U.1),
        η k U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η k U V h x) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
        (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U.1), (F' k).res hV (η k U V₂ h₂ x) = η k U V₁ h₁ x) ∧

      (∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
        (hU : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1), η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU x)) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : (F (k + 1)).obj U.1),
        (φ' k).app V (η (k + 1) U V h x) = η k U V h ((φ k).app U x)) ∧

      (∀ (k : ℕ) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
        letI := (p.appLE U.1 V.1 h).hom.toAlgebra
        ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] (F k).obj U.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
          ∀ x : (F k).obj U.1, β (1 ⊗ₜ x) = η k U V h x) ∧

      (∀ (k : ℕ) (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1),
        IsIso (p ∣_ W.1) → Function.Bijective (η k W W' hW.le)) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom.solution I q p F hc hq φ hφs hφk
