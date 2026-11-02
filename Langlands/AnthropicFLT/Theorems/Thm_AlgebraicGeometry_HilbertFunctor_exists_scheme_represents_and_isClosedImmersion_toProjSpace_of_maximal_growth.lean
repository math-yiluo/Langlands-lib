/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AlgebraicGeometry.ULiftIntAlgebra
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type uz) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1)) :
    (∀ (A B : Type uz) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h),
        ∃ Q : Point B n h, Q.I = Ideal.map (MvPolynomial.map φ) P.I) ∧
    ∃ (Hilb : Scheme.{uz})
      (pt : ∀ (A : Type uz) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
      (∀ (A B : Type uz) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h) (Q : Point B n h),
          Q.I = Ideal.map (MvPolynomial.map φ) P.I →
          pt B Q = Spec.map (CommRingCat.ofHom φ) ≫ pt A P) ∧
      ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
        IsClosedImmersion ι :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.solution n m h h₁ h₂ h₃
