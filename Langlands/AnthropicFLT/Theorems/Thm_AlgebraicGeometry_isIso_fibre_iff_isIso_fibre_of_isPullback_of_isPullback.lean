/-
Ported from `Theorems/Thm_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback
    {X Y Z X' Y' Z' : Scheme.{uz}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (p' : Z' ⟶ Y') (q' : X' ⟶ Y') (h' : Z' ⟶ X') (w' : h' ≫ q' = p')
    (π : Y' ⟶ Y) (πZ : Z' ⟶ Z) (πX : X' ⟶ X)
    (hZ : IsPullback πZ p' p π) (hX : IsPullback πX q' q π) (hh : h' ≫ πX = πZ ≫ h) (y' : Y') :
    IsIso (pullback.map p' (Y'.fromSpecResidueField y') q' (Y'.fromSpecResidueField y') h' (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w']) (by rw [Category.comp_id, Category.id_comp])) ↔
      IsIso (pullback.map p (Y.fromSpecResidueField (π.base y')) q (Y.fromSpecResidueField (π.base y')) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) :=
  P2MW.S_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback.solution p q h w p' q' h' w' π πZ πX hZ hX hh y'
