/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
    (R : Type uz) [CommRing R] (n : ℕ) (h : ℕ → ℕ)
    (hbc : ∀ (A B : Type uz) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h),
        ∃ Q : Point B n h, Q.I = Ideal.map (MvPolynomial.map φ) P.I)
    (Hilb : Scheme.{uz}) (πH : Hilb ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type uz) [CommRing A] (ψ : R →+* A),
      Point A n h ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom ψ)) πH)
    (hnat : ∀ (A B : Type uz) [CommRing A] [CommRing B] (ψ : R →+* A) (φ : A →+* B) (P : Point A n h) (Q : Point B n h),
        Q.I = Ideal.map (MvPolynomial.map φ) P.I →
        (pt B (φ.comp ψ) Q).1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt A ψ P).1)
    (I₀ : Ideal (MvPolynomial (Fin (n + 1)) R)) (hI₀ : ∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀)
    (hfg : I₀.FG) (m : ℕ) :
    ∃ (C : Scheme.{uz}) (ι : C ⟶ Hilb), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (A : Type uz) [CommRing A] (ψ : R →+* A) (P : Point A n h),
        (∃ c : Spec (CommRingCat.of A) ⟶ C, c ≫ ι = (pt A ψ P).1) ↔
          ∀ (d : ℕ), m ≤ d → ∀ F : MvPolynomial (Fin (n + 1)) A,
            F ∈ Ideal.map (MvPolynomial.map ψ) I₀ → F.IsHomogeneous d → F ∈ P.I :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.solution R n h hbc Hilb πH pt hnat I₀ hI₀ hfg m
