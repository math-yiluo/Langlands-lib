/-
Ported from `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AlgebraicGeometry.ULiftIntAlgebra
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] Langlands.ULiftInt.algebra in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type uz) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ (Hilb : Scheme.{uz}) (p : Hilb ⟶ Spec (CommRingCat.of (ULift.{uz} ℤ)))
        (pt : ∀ (A : Type uz) [CommRing A],
          Point A n (hilbertFunctionOf n P m) ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
        (∀ (A B : Type uz) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)),
            ∃ y : Point B n (hilbertFunctionOf n P m), y.I = Ideal.map (MvPolynomial.map φ) x.I) ∧
        (∀ (A B : Type uz) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)) (y : Point B n (hilbertFunctionOf n P m)),
            y.I = Ideal.map (MvPolynomial.map φ) x.I ↔
            pt B y = Spec.map (CommRingCat.ofHom φ) ≫ pt A x) ∧
        (∀ (A : Type uz) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
            pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) A))) ∧
        IsProper p ∧ LocallyOfFinitePresentation p ∧
        (∀ F : Finset Hilb, ∃ U : Hilb.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
        ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
          IsClosedImmersion ι ∧ ι ≫ ProjSpace.π (ULift.{uz} ℤ) N = p := by
  obtain ⟨D₀, hD₀⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
      n P hP
  refine ⟨D₀, fun m hm => ?_⟩
  obtain ⟨hbc, Hilb, pt, hnat, N, ι, hι⟩ := hD₀ m hm
  haveI : IsClosedImmersion ι := hι

  refine ⟨Hilb, ι ≫ ProjSpace.π (ULift.{uz} ℤ) N, pt, hbc, ?_, ?_, ?_, ?_, ?_, N, ι, hι, rfl⟩
  ·
    intro A B _ _ φ x y
    refine ⟨hnat A B φ x y, fun h => ?_⟩
    obtain ⟨y', hy'⟩ := hbc A B φ x
    have hyy' : y' = y := (pt B).injective ((hnat A B φ x y' hy').trans h.symm)
    rw [← hyy']
    exact hy'
  ·
    intro A _ x
    exact specULiftZIsTerminal.hom_ext _ _
  ·
    infer_instance
  ·
    haveI : IsNoetherianRing (CommRingCat.of (ULift.{uz} ℤ)) := inferInstanceAs (IsNoetherianRing (ULift.{uz} ℤ))
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{uz} ℤ))) := inferInstance
    infer_instance
  ·
    intro F
    exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ)) ι F
