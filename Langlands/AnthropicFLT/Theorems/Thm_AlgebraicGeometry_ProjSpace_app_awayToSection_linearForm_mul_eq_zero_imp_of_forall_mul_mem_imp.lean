/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp
    (n m : ℕ) (k : Type uz) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (Zk : Scheme.{uz}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)))
    (a : Fin (n + 1) → k)
    (hnzd : ∀ e : ℕ, m ≤ e → ∀ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous e →
      (∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j) * f ∈ J → f ∈ J) :
    ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := 1
                num := ⟨(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j), (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                  (MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X (a j) j)⟩
                den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0 :=
  P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.solution n m k J Zk ιk hZ a hnzd
