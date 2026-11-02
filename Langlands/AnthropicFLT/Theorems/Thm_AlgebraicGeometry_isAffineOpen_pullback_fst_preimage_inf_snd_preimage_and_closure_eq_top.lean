/-
Ported from `Theorems/Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
    Subring.closure
      (Set.range (fun s : Γ(X, U) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_left : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ U)).op
            ((pullback.fst f g).app U s)) ∪
        Set.range (fun t : Γ(Y, V) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_right : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.snd f g ⁻¹ᵁ V)).op
            ((pullback.snd f g).app V t))) = ⊤ :=
  P2MW.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top.solution f g hU hV
