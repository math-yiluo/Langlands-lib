/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
    (E : Scheme.{u})
    (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
    (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.solution E I hI
