/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (e : ℕ) (m : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
    (hm : m ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (e : ℤ)) (j : Fin (n + 1)) :
    ∃ (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous (e + k)),
      ∀ i : Fin (n + 1),
        (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) m) ((e + k : ℕ) : ℤ) i =
          ProjSpace.restrictFun
            (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
            ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := e + k
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule (e + k) F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ (e + k), (MvPolynomial.mem_homogeneousSubmodule (e + k) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (e + k))⟩
                    den_mem := ⟨e + k, rfl⟩ }))) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.solution ι e m hm j
