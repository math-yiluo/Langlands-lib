/-
Ported from `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (k : Type uz) [Field k]
    (Zk : Scheme.{uz}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hZ : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ I ↔ ∀ i : Fin (n + 1),
            (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0))
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d)
    (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) :
    F ∈ I := by
  rw [hZ d F hF]
  intro i
  obtain ⟨N, hN⟩ := hsat i
  have hG : (X i ^ N * F).IsHomogeneous (N + d) := (MvPolynomial.isHomogeneous_X_pow i N).mul hF
  have h := (hZ (N + d) (X i ^ N * F) hG).mp hN i

  have heq : (HomogeneousLocalization.mk
      { deg := N + d
        num := ⟨X i ^ N * F, (MvPolynomial.mem_homogeneousSubmodule (N + d) _).mpr hG⟩
        den := ⟨MvPolynomial.X i ^ (N + d), (MvPolynomial.mem_homogeneousSubmodule (N + d) _).mpr
          (MvPolynomial.isHomogeneous_X_pow i (N + d))⟩
        den_mem := ⟨N + d, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
      = (HomogeneousLocalization.mk
      { deg := d
        num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
        den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (MvPolynomial.isHomogeneous_X_pow i d)⟩
        den_mem := ⟨d, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i)) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; ring⟩
  rw [← heq]
  exact h
