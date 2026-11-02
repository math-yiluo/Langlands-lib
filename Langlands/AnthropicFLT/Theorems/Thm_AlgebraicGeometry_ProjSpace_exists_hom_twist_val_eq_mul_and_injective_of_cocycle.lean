/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle
    {A : Type u} [CommRing A] {N : ℕ} {Z : Scheme.{u}}
    (π : Z ⟶ Spec (.of A)) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom ι]
    (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, ProjSpace.pullbackChart ι i))
    (htc : ∀ i j : Fin (N + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _) (t i)
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _)
            (ProjSpace.frameUnit ι i j) ^ e
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _) (t j))
    (hnz : ∀ (i : Fin (N + 1)) (y : Γ(Z, ProjSpace.pullbackChart ι i)), t i * y = 0 → y = 0) (d : ℕ) :
    ∃ μ : OModulePresheaf.Hom (ProjSpace.twist π ι d) (ProjSpace.twist π ι (d + e)),
      (∀ (U : Z.Opens) (g : (ProjSpace.twist π ι d).obj U) (i : Fin (N + 1)),
        (μ.app U g).val i
          = ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ι i ≤ _) (t i) * g.val i) ∧
      (∀ U : Z.Opens, Function.Injective (μ.app U)) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle.solution π ι e t htc hnz d
