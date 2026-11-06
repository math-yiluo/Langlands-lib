/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (G : OModulePresheaf q) (hq : G.IsQuasicoherent)
    {i : ℕ} (c : Fin (i + 1) → Fin (r + 1)) (d : ℕ) (t : G.obj (⨅ v, ProjSpace.pullbackChart ι (c v))) :
    ∃ (N : ℕ) (t' : ∀ j : Fin (r + 1), G.obj (ProjSpace.pullbackChart ι j)),
      OModulePresheaf.FramesCompat ι G (d + N * (i + 1)) t' ∧
      ∀ j : Fin (r + 1),
        G.res (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
            (t' j) =
          ((∏ v : Fin (i + 1), ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c v))) ^ N *
              ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c 0)) ^ d) •
            G.res (inf_le_right : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ⨅ v, ProjSpace.pullbackChart ι (c v)) t :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution ι G hq c d t
