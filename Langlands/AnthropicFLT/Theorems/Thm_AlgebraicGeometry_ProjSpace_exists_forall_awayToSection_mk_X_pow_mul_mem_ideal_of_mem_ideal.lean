/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
    (n : ℕ) (A : Type uz) [CommRing A] (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (i : Fin (n + 1)) (a : ℕ) (H : MvPolynomial (Fin (n + 1)) A) (hH : H.IsHomogeneous a)
    (hmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ }) ∈
      𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ j : Fin (n + 1),
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
        (HomogeneousLocalization.mk
          { deg := N + a
            num := ⟨X i ^ N * H, (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr ((MvPolynomial.isHomogeneous_X_pow i N).mul hH)⟩
            den := ⟨X j ^ (N + a), (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr (MvPolynomial.isHomogeneous_X_pow j (N + a))⟩
            den_mem := ⟨N + a, rfl⟩ }) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.solution n A 𝓘 i a H hH hmem N₀
