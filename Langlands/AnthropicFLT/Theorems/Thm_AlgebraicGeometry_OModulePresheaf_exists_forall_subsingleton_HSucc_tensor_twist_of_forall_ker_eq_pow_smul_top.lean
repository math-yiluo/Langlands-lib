/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKc : ∀ k, (K k).IsCoherent) (hKq : ∀ k, (K k).IsQuasicoherent)
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : P.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (k i : ℕ),
      Subsingleton (((K k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.solution I ι hιq F hc hq φ hφs hφk K hKc hKq j hji hjr
