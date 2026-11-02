/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal
    (R : Type uz) [CommRing R]
    (F : ∀ (A : Type uz) [CommRing A] [Algebra R A], Type uz)
    (Fmap : ∀ (A B : Type uz) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (X : Scheme.{uz}) (p : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type uz) [CommRing A] [Algebra R A],
      F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (pt_natural : ∀ (A B : Type uz) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : F A),
      (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1)
    (W : ∀ (A : Type uz) [CommRing A] [Algebra R A], F A → Prop)
    (closed : ∀ (A : Type uz) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
      ∀ (B : Type uz) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0) :
    ∃ (Z : Scheme.{uz}) (ι : Z ⟶ X)
      (ptZ : ∀ (A : Type uz) [CommRing A] [Algebra R A],
        {s : F A // W A s} ≃
          {g : Spec (CommRingCat.of A) ⟶ Z //
            g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      IsClosedImmersion ι ∧
      ∀ (A : Type uz) [CommRing A] [Algebra R A] (s : {s : F A // W A s}),
        (ptZ A s).1 ≫ ι = (pt A s.1).1 :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.solution R F Fmap X p pt pt_natural W closed
