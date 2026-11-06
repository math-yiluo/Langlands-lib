/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (F : OModulePresheaf q) (F' : OModulePresheaf (p ≫ q))
    (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (F.obj U.1 →ₗ[A] F'.obj V.1))
    (hηs : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : F.obj U.1),
      η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x)
    (hηV : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : F.obj U.1), F'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x)
    (hηU : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : F.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (F.res hU x)) :
    ∃ v : OModulePresheaf.AffHom F (OModulePresheaf.cechPushforward p q K' F'),
      ∀ (U : P.affineOpens) (x : F.obj U.1) (j : K'.ι),
        (v.app U x).1 j = η U (OModulePresheaf.AffHom.affineChart p q K' U j)
          (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq.solution q p K' F F' η hηs hηV hηU
