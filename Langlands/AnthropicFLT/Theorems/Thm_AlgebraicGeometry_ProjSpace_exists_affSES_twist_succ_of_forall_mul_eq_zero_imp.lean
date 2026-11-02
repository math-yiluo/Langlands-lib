/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
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
    (hker : ι'.ker = ιk.ker ⊔ 𝓘ℓ) (d : ℕ) :
    ∃ (F₃ : OModulePresheaf (ιk ≫ ProjSpace.π k n))
      (S : OModulePresheaf.AffSES (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d)
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)) F₃)
      (e₀ : F₃.H0 (ProjSpace.stdCoverPullback ιk) ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).H0 (ProjSpace.stdCoverPullback ι'))
      (_e : ∀ i : ℕ, F₃.HSucc (ProjSpace.stdCoverPullback ιk) i ≃ₗ[k]
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
            ((e₀ (S.proj.H0Map (ProjSpace.stdCoverPullback ιk) ⟨c, hc⟩)).1 s).val i =
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
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.solution n k Zk ιk ℓ hℓ hnzd 𝓘ℓ h𝓘ℓ Z' ι' hker d
