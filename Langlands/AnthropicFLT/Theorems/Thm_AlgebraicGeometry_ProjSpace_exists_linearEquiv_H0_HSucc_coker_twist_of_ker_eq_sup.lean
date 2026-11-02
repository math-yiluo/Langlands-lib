/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
    (n : ℕ) (k : Type uz) [CommRing k]
    (Zk : Scheme.{uz}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)
    (hnzd : ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
      (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (HomogeneousLocalization.mk
            { deg := 1
              num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
              den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
              den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0)
    (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData)
    (h𝓘ℓ : (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {ℓ} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }))
    (Z' : Scheme.{uz}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι']
    (hker : ι'.ker = ιk.ker ⊔ 𝓘ℓ) (d : ℕ)
    (htc : ∀ i j : Fin (n + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                  den_mem := ⟨1, rfl⟩ })))
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
            (ProjSpace.frameUnit ιk i j) ^ 1
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X j ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow j 1)⟩
                  den_mem := ⟨1, rfl⟩ }))))
    (μ : OModulePresheaf.Hom (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d)
      (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)))
    (hμ : ∀ (U : Zk.Opens) (g : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).obj U) (i : Fin (n + 1)),
      (μ.app U g).val i
        = ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ιk i ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                  den_mem := ⟨1, rfl⟩ }))) * g.val i) :
    ∃ (e₀ : (OModulePresheaf.coker μ).H0 (ProjSpace.stdCoverPullback ιk) ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).H0 (ProjSpace.stdCoverPullback ι'))
      (_e : ∀ i : ℕ, (OModulePresheaf.coker μ).HSucc (ProjSpace.stdCoverPullback ιk) i ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).HSucc (ProjSpace.stdCoverPullback ι') i),
      ∀ (c : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).cochain (ProjSpace.stdCoverPullback ιk) 0)
        (hc : c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).H0 (ProjSpace.stdCoverPullback ιk))
        (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous (d + 1)),
          (∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                  ProjSpace.pullbackChart ιk i)
                (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ })))) →
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            ((e₀ ((OModulePresheaf.imCokerSES μ).proj.toAffHom.H0Map (ProjSpace.stdCoverPullback ιk) ⟨c, hc⟩)).1 s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' i ≤
                  ProjSpace.pullbackChart ι' i)
                (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ }))) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup.solution n k Zk ιk ℓ hℓ hnzd 𝓘ℓ h𝓘ℓ Z' ι' hker d htc μ hμ
