/-
Ported from `Theorems/Thm_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u

theorem Ideal.exists_forall_iff_map_eq_bot_of_forall_away
    (A : Type u) [CommRing A]
    (P : ∀ (A' : Type u) [CommRing A'], (A →+* A') → Prop)
    (hPmap : ∀ (A' A'' : Type u) [CommRing A'] [CommRing A''] (χ : A' →+* A'') (φ : A →+* A'),
      P A' φ → P A'' (χ.comp φ))
    (hPloc : ∀ (A' : Type u) [CommRing A'] (φ : A →+* A') (κ : Type u) (s : κ → A'),
      Ideal.span (Set.range s) = ⊤ →
      (∀ k, P (Localization.Away (s k)) ((algebraMap A' (Localization.Away (s k))).comp φ)) → P A' φ)
    (κ : Type u) (r : κ → A) (hr : Ideal.span (Set.range r) = ⊤)
    (K : ∀ i : κ, Ideal (Localization.Away (r i)))
    (hK : ∀ (i : κ) (A' : Type u) [CommRing A'] (χ : Localization.Away (r i) →+* A'),
      P A' (χ.comp (algebraMap A (Localization.Away (r i)))) ↔ Ideal.map χ (K i) = ⊥) :
    ∃ I : Ideal A, ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'), P A' φ ↔ Ideal.map φ I = ⊥ :=
  P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.solution A P hPmap hPloc κ r hr K hK
