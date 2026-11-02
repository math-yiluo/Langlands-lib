/-
Ported from `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (B : Type u) [CommRing B] [Algebra A B] :
    ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
      (_ : IsClosedImmersion ι') (e : Z' ⟶ Z),
      IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      e ≫ ι = ι' ≫ ProjSpace.map A B n := by
  refine ⟨pullback ι (ProjSpace.map A B n), pullback.snd ι (ProjSpace.map A B n), inferInstance,
    pullback.fst ι (ProjSpace.map A B n), ?_, pullback.condition⟩
  exact (IsPullback.of_hasPullback ι (ProjSpace.map A B n)).paste_vert (ProjSpace.isPullback_map A B n)
