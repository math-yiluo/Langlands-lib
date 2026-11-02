/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (π : X ⟶ Spec (.of A)) (m : ℕ) :
    ∃ e : ∀ (I : Finset (Fin (N + 1))), I.Nonempty →
        (ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I
          ≃ₗ[A] ProjSpace.twistObj π φ m (⨅ i ∈ I, ProjSpace.pullbackChart φ i)),
      ∀ (I J : Finset (Fin (N + 1))) (hI : I.Nonempty) (hIJ : I ⊆ J)
        (x : ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I),
        e J (hI.mono hIJ) (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
          = ProjSpace.twistRes π φ m
              (le_iInf fun i => le_iInf fun hi => (iInf_le _ i).trans (iInf_le _ (hIJ hi)) :
                (⨅ i ∈ J, ProjSpace.pullbackChart φ i) ≤ ⨅ i ∈ I, ProjSpace.pullbackChart φ i)
              (e I hI x) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.solution φ π m
