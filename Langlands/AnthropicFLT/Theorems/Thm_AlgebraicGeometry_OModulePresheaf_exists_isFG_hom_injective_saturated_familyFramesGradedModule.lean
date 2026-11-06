/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsClosedImmersion ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (G : ℕ → OModulePresheaf q) (hc : ∀ k, (G k).IsCoherent) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) :
    ∃ (D : ProjSpaceCech.GradedModule (MvPolynomial (Fin s) A) r) (_ : ProjSpaceCech.GradedModule.IsFG D)
      (h : ProjSpaceCech.GradedModule.Hom D (OModulePresheaf.familyFramesGradedModule ι G θ hθ)),
      Function.Injective h.toLinearMap ∧
      ∀ (e : ℤ) (f : (OModulePresheaf.familyFramesGradedModule ι G θ hθ).M),
        f ∈ (OModulePresheaf.familyFramesGradedModule ι G θ hθ).grade e → ∀ l : Fin (r + 1),
          ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧
            h.toLinearMap f' = ((OModulePresheaf.familyFramesGradedModule ι G θ hθ).xMul l ^ N) f :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.solution ι hιq G hc hq θ hθ hgen
