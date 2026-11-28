import Langlands.Global.ArchimedeanComplexifiedPlaces
import Langlands.Global.InfiniteAdelicRealTrace

/-! # Complex coordinates of the infinite adele coefficient algebra -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]

omit [NumberField F] in
private theorem extensionEmbedding_algebraMap_real (v : InfinitePlace F) (r : ℝ) :
    letI := InfinitePlaceGroupPoints.completionRCLike F v
    InfinitePlace.Completion.extensionEmbedding v (algebraMap ℝ v.Completion r) = (r : ℂ) := by
  let := InfinitePlaceGroupPoints.completionRCLike F v
  let e := InfinitePlace.Completion.extensionEmbedding v
  have h : (fun x : ℝ => e (algebraMap ℝ v.Completion x)) = Complex.ofReal := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
        (continuous_algebraMap ℝ v.Completion)
    · exact Complex.continuous_ofReal
    · funext q
      change e (algebraMap ℝ v.Completion (q : ℝ)) = Complex.ofRealHom (q : ℝ)
      rw [map_ratCast, map_ratCast, map_ratCast]
  exact congrFun h r

/-- The mixed real and complex coordinates of the infinite adeles respect the real scalar
structure given by the completion manifolds. -/
def mixedSpaceRealAlgEquiv :
    letI := realAlgebra F
    InfiniteAdeleRing F ≃ₐ[ℝ] mixedEmbedding.mixedSpace F := by
  letI := realAlgebra F
  refine AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace F) fun r => ?_
  rw [realAlgebra_algebraMap, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · apply Complex.ofReal_injective
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_algebraMap_real F v.1 r
  · exact extensionEmbedding_algebraMap_real F v.1 r

/-- The complexification of the actual infinite adele ring has one complex factor at a
real place and two complex factors at a complex place. -/
def complexifiedAdeleCoordinates :
    letI := realAlgebra F
    (ℂ ⊗[ℝ] InfiniteAdeleRing F) ≃ₐ[ℂ] (ArchimedeanGL.ComplexifiedPlace F → ℂ) :=
  letI := realAlgebra F
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) (mixedSpaceRealAlgEquiv F)).trans
    (ArchimedeanGL.complexifiedScalarCoordinates F)

/-- Evaluation of an infinite adele at a complexified place, as a real algebra map. -/
def complexifiedAdeleEvaluation (v : ArchimedeanGL.ComplexifiedPlace F) :
    letI := realAlgebra F
    InfiniteAdeleRing F →ₐ[ℝ] ℂ :=
  letI := realAlgebra F
  let coord := (Pi.evalAlgHom ℂ _ v).comp (complexifiedAdeleCoordinates F).toAlgHom
  (coord.restrictScalars ℝ).comp Algebra.TensorProduct.includeRight

@[simp]
theorem complexifiedAdeleCoordinates_tmul (c : ℂ) (x : InfiniteAdeleRing F)
    (v : ArchimedeanGL.ComplexifiedPlace F) :
    letI := realAlgebra F
    complexifiedAdeleCoordinates F (c ⊗ₜ[ℝ] x) v = c * complexifiedAdeleEvaluation F v x := by
  let := realAlgebra F
  have h := (complexifiedAdeleCoordinates F).commutes c
  change complexifiedAdeleCoordinates F (c ⊗ₜ[ℝ] (1 : InfiniteAdeleRing F)) =
    algebraMap ℂ (ArchimedeanGL.ComplexifiedPlace F → ℂ) c at h
  change _ = c * complexifiedAdeleCoordinates F (1 ⊗ₜ[ℝ] x) v
  calc
    _ = complexifiedAdeleCoordinates F ((c ⊗ₜ[ℝ] 1) * (1 ⊗ₜ[ℝ] x)) v := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by rw [map_mul, h]; rfl

end Langlands.Global.InfiniteAdelicGroupPoints
