/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
attribute [-simp] AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
    (A : Type uz) [CommRing A] (n : ℕ) (Z : Scheme.{uz})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    [IsClosedImmersion ι] [LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n)] :
    ∃ I₀ : Ideal (MvPolynomial (Fin (n + 1)) A), I₀.FG ∧
      (∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀) ∧
      ∀ i : Fin (n + 1),
        ι.ker.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
          Ideal.span {a | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d), F ∈ I₀ ∧
            a = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })} :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.solution A n Z ι
