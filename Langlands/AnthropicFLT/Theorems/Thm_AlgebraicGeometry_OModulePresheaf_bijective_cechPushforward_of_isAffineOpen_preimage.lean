/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent)
    (W : P.affineOpens) (hW : IsAffineOpen (p ⁻¹ᵁ W.1)) :
    (∀ x y : G.obj (p ⁻¹ᵁ W.1),
        (∀ j : K'.ι, G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x
          = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) y) → x = y) ∧
      ∀ c : (OModulePresheaf.cechPushforward p q K' G).obj W.1,
        ∃ x : G.obj (p ⁻¹ᵁ W.1), ∀ j : K'.ι,
          c.1 j = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.solution q p K' G hqc W hW
