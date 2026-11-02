/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (d : ℕ) :
    ∃ ε : ∀ i : ℕ,
        B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i ≃ₗ[B]
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain (ProjSpace.stdCoverPullback ι') i,
      (∀ i : ℕ,
        (ε (i + 1)).toLinearMap ∘ₗ ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i).baseChange B =
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i ∘ₗ (ε i).toLinearMap) ∧
      (∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)
        (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
        (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
          e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
        (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
          ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)) ((c s).val j))) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.solution ι B ι' e hpb hcomp d
