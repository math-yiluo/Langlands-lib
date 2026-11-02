/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut
    (H : Scheme.{u})
    (Q : ∀ (A : Type u) [CommRing A], (Spec (CommRingCat.of A) ⟶ H) → Prop)

    (hQmap : ∀ (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A') (u : Spec (CommRingCat.of A) ⟶ H),
      Q A u → Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u))

    (hQloc : ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H) (ι : Type u) (r : ι → A),
      Ideal.span (Set.range r) = ⊤ →
      (∀ i, Q (Localization.Away (r i))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r i)))) ≫ u)) → Q A u)

    (hQcut : ∀ (U : H.Opens) (hU : IsAffineOpen U) (B : Type u) [CommRing B]
      (e : Spec (CommRingCat.of B) ≅ (U : Scheme.{u})),
      ∃ J : Ideal B, ∀ (A : Type u) [CommRing A] (φ : B →+* A),
        Q A (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ↔ Ideal.map φ J = ⊥) :
    ∃ (C : Scheme.{u}) (ι : C ⟶ H), IsClosedImmersion ι ∧
      ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H),
        (∃ v : Spec (CommRingCat.of A) ⟶ C, v ≫ ι = u) ↔ Q A u :=
  P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.solution H Q hQmap hQloc hQcut
