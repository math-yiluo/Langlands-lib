import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.Algebra.RationalPolynomialFiniteDifference

/-! # Euler-sequence differences and coherent graph comparison -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules QuasicoherentLocal

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsLocallyNoetherian X]

/-- The indicated iterated difference of the actual coherent Euler sequence vanishes. -/
def HasVanishingEulerDifference (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ) : Prop :=
  (fwdDiff 1)^[d] (coherentEulerSequence f M hM L) = 0

/-- The iterated rational forward difference commutes with subtraction. -/
lemma iterate_fwdDiff_sub (a b : ℕ → ℚ) (e : ℕ) :
    (fwdDiff 1)^[e] (a - b) = (fwdDiff 1)^[e] a - (fwdDiff 1)^[e] b := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub (fwdDiff_aux.fwdDiffₗ ℕ ℚ 1 ^ e) a b

/-- The iterated rational forward difference sends zero to zero. -/
lemma iterate_fwdDiff_zero (e : ℕ) : (fwdDiff 1)^[e] (0 : ℕ → ℚ) = 0 := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_zero (fwdDiff_aux.fwdDiffₗ ℕ ℚ 1 ^ e)

/-- The difference of source and target Euler sequences is that of kernel and cokernel. -/
lemma coherentEulerSequence_sub {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L : Picard.LineBundle X) :
    letI := isQuasicoherent_kernel φ
    letI := isQuasicoherent_cokernel φ
    coherentEulerSequence f M hM L - coherentEulerSequence f N hN L =
      coherentEulerSequence f (kernel φ) (hM.kernel φ) L -
        coherentEulerSequence f (cokernel φ) (hN.cokernel φ) L := by
  have := isQuasicoherent_image φ
  have := isQuasicoherent_kernel φ
  have := isQuasicoherent_cokernel φ
  let p := factorThruImage φ
  let i := image.ι φ
  have := isQuasicoherent_kernel p
  have := isQuasicoherent_cokernel i
  have hI : HasFiniteAffineSections (image φ) := hM.of_epi p
  let S₁ := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let S₂ := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  have h₁ := coherentEulerSequence_add f S₁ hS₁ (hM.kernel p) hM hI L
  have h₂ := coherentEulerSequence_add f S₂ hS₂ hI hN (hN.cokernel i) L
  let eK : kernel φ ≅ kernel p :=
    (kernelIsoOfEq (image.fac φ)).symm ≪≫ kernelCompMono p i
  let eC : cokernel φ ≅ cokernel i :=
    (cokernelIsoOfEq (image.fac φ)).symm ≪≫ cokernelEpiComp p i
  have hK := coherentEulerSequence_iso f (hM.kernel φ) (hM.kernel p) L eK
  have hC := coherentEulerSequence_iso f (hN.cokernel φ) (hN.cokernel i) L eC
  change coherentEulerSequence f M hM L = _ at h₁
  change coherentEulerSequence f N hN L = _ at h₂
  rw [h₁, h₂, hK, hC]
  abel

/-- Smaller-support vanishing makes an affine graph comparison invisible to the top difference. -/
lemma iterate_fwdDiff_sub_of_graph [X.IsSeparated] (d : ℕ)
    (ih : ∀ (A : X.Modules) [A.IsQuasicoherent] (hA : HasFiniteAffineSections A)
      (L : Picard.LineBundle X),
      HasSupportDimensionLT A d → (fwdDiff 1)^[d] (coherentEulerSequence f A hA L) = 0)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L : Picard.LineBundle X) (T : IrreducibleCloseds X) (hT : height T ≤ d)
    (U : X.Opens) (hU : IsAffineOpen U) (hTU : ((T : Set X) ∩ U).Nonempty)
    (hMT : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hNT : VanishesOn N ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (e : N.restrict U.ι ≅ M.restrict U.ι) :
    (fwdDiff 1)^[d] (coherentEulerSequence f N hN L - coherentEulerSequence f M hM L) = 0 := by
  have := CoherentGraph.isQuasicoherent M N U e hU
  obtain ⟨hK₁, hC₁, hK₂, hC₂⟩ := CoherentGraph.isQuasicoherent_errors M N U e hU
  obtain ⟨hFK₁, hFC₁, hFK₂, hFC₂⟩ :=
    CoherentGraph.hasFiniteAffineSections_errors M N U e hU hM hN
  obtain ⟨hDK₁, hDC₁, hDK₂, hDC₂⟩ :=
    CoherentGraph.lowerSupportErrors M N U e T hT hTU hMT hNT
  have hG := CoherentGraph.hasFiniteAffineSections M N U e hM hN
  have h₁ := coherentEulerSequence_sub f (CoherentGraph.fst M N U e) hG hM L
  have h₂ := coherentEulerSequence_sub f (CoherentGraph.snd M N U e) hG hN L
  have hEq : coherentEulerSequence f N hN L - coherentEulerSequence f M hM L =
      (coherentEulerSequence f (kernel (CoherentGraph.fst M N U e)) hFK₁ L -
        coherentEulerSequence f (cokernel (CoherentGraph.fst M N U e)) hFC₁ L) -
      (coherentEulerSequence f (kernel (CoherentGraph.snd M N U e)) hFK₂ L -
        coherentEulerSequence f (cokernel (CoherentGraph.snd M N U e)) hFC₂ L) := by
    rw [← h₁, ← h₂]
    abel
  rw [hEq, iterate_fwdDiff_sub, iterate_fwdDiff_sub, iterate_fwdDiff_sub,
    ih _ hFK₁ L hDK₁, ih _ hFC₁ L hDC₁, ih _ hFK₂ L hDK₂, ih _ hFC₂ L hDC₂]
  simp

end Langlands.AlgebraicGeometry.Modules.DerivedSections
