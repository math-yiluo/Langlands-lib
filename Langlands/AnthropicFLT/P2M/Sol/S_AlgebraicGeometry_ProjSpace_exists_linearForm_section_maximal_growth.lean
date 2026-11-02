/-
Ported from `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearForm_section_maximal_growth.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp
import Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth
import Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearForm_section_maximal_growth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n m : ℕ) (hm : 1 ≤ m) (k : Type uz) [Field k] [Infinite k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank k (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J m)))
    (Zk : Scheme.{uz}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0))) :
    ∃ a : Fin (n + 1) → k,

      (∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := 1
                num := ⟨(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j), (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                  (MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X (a j) j)⟩
                den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0) ∧

      (∀ (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData),
        (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) →
        ∀ (Z' : Scheme.{uz}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι'],
          ι'.ker = ιk.ker ⊔ 𝓘ℓ →
          let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
            Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
          Module.finrank k (piece J' (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J' m)) ∧
          (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J' ↔ ∀ i : Fin (n + 1), (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)) ∧
          (0 < Module.finrank k (piece J m) → Module.finrank k (piece J' m) < Module.finrank k (piece J m))) := by
  classical
  obtain ⟨G₁, hG₁0, hG₁⟩ :=
    MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow n m k J hJ hmax
  obtain ⟨G₂, hG₂0, hG₂⟩ :=
    MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow n m k J hJ hmax

  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → k, MvPolynomial.eval a (G₁ * G₂) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hG₁0 hG₂0 (MvPolynomial.funext fun x => by rw [h x, map_zero])
  have ha₁ : MvPolynomial.eval a G₁ ≠ 0 := fun h0 => ha (by rw [map_mul, h0, zero_mul])
  have ha₂ : MvPolynomial.eval a G₂ ≠ 0 := fun h0 => ha (by rw [map_mul, h0, mul_zero])
  have hnzd := hG₁ a ha₁
  obtain ⟨-, hgrowth, hsum⟩ := hG₂ a ha₂
  refine ⟨a, AlgebraicGeometry.ProjSpace.app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp n m k J Zk ιk hZ a hnzd,
    fun 𝓘ℓ h𝓘 Z' ι' _ hker => ?_⟩
  obtain ⟨hii, hiv⟩ := MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt n m hm k J hJ a hgrowth hsum
  exact ⟨hii, AlgebraicGeometry.ProjSpace.mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth n m hm k J hJ Zk ιk hZ a hii
    𝓘ℓ h𝓘 Z' ι' hker, hiv⟩
