/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_H0_tensor_twist_span_eq_top
    {A : Type u} [CommRing A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      ∃ (m : ℕ) (σ : Fin m → ↥((F.tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι))),
        ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
          Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
              (Set.range fun l : Fin m =>
                (σ l : (F.tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤ :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.solution ι hιq F hc hq
