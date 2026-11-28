import Langlands.Global.AdelicLeviCenterTransferReduction
import Langlands.Automorphic.GroupSchemeParabolicTangentStatement
import Langlands.Automorphic.GroupSchemeEnvelopingAction
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Global.InfiniteAdelicLeviEnveloping

/-! # Differentials of homomorphisms on actual infinite adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine H.X.left]
  {d e : ℕ}

/-- The complex-linear extension of the real Lie algebra map `pointTangentLieHom`. -/
def complexPointLieDifferential (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom)
    (f : H ⟶ G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothLieGroup F G hG
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    letI := smoothChartedSpace F H hH
    letI := smoothLieGroup F H hH
    letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
    ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H) →ₗ⁅ℂ⁆
      ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  letI := smoothLieGroup F G hG
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI := smoothChartedSpace F H hH
  letI := smoothLieGroup F H hH
  letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  exact Langlands.Algebra.ComplexLieExtension.extendLieHom (pointTangentLieHom F hH hG f)

/-- Its underlying linear map is `complexPointDifferential`, the base change of the derivative
at `1`. -/
theorem complexPointLieDifferential_apply (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom)
    (f : H ⟶ G) (Z : AdelicComplexLieAlgebra F H hH) :
    complexPointLieDifferential hH hG f Z = complexPointDifferential F hH hG f Z := rfl

/-- Pullback intertwines the real differential with its image under the derivative. -/
theorem pointPullback_plotSmoothDifferential (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom) (f : H ⟶ G)
    (X : smoothModel F e) (u : InfinitePlotSmoothFunctions F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothChartedSpace F H hH
    Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f (plotSmoothDifferential F G hG
        (mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
          (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F))) 1 X) u) =
      plotSmoothDifferential F H hH X (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f u) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let := smoothChartedSpace F H hH
  let := smoothLieGroup F H hH
  apply Subtype.ext
  funext x
  have hu := (isPlotSmooth_iff_contMDiff F G hG u.val).mp u.property
  exact (groupDirectionalValue_comp_hom 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
    (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)))
    (contMDiff_affinePointsTarget F hH hG f) X hu x).symm

/-- Pullback intertwines the complexified enveloping actions through the enveloping map of the
complexified Lie differential. -/
theorem pointPullback_envelopingAction (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom)
    (hcH : AdelicDifferentialCommutator F H hH) (hcG : AdelicDifferentialCommutator F G hG)
    (f : H ⟶ G) (w : AdelicEnvelopingAlgebra F H hH) (u : InfinitePlotSmoothFunctions F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothLieGroup F G hG
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    letI := smoothChartedSpace F H hH
    letI := smoothLieGroup F H hH
    letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
    Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f (plotSmoothEnvelopingAction F G hG hcG
        (UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
          (complexPointLieDifferential hH hG f)) w) u) =
      plotSmoothEnvelopingAction F H hH hcH w (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f u) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let := smoothChartedSpace F H hH
  let := smoothLieGroup F H hH
  let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H))) w
  change Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f (plotSmoothEnvelopingAction F G hG hcG
      (UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
        (complexPointLieDifferential hH hG f))
          (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)) u) =
    plotSmoothEnvelopingAction F H hH hcH (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)
      (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f u)
  induction t using TensorAlgebra.induction generalizing u with
  | algebraMap z =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | «ι» Z =>
    change Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f (plotSmoothEnvelopingAction F G hG hcG
        (UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
          (complexPointLieDifferential hH hG f))
            (UniversalEnvelopingAlgebra.ι ℂ Z)) u) =
      plotSmoothEnvelopingAction F H hH hcH (UniversalEnvelopingAlgebra.ι ℂ Z)
        (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f u)
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    simp only [LieHom.coe_comp, Function.comp_apply, plotSmoothEnvelopingAction_generator]
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      rw [complexPointLieDifferential, Langlands.Algebra.ComplexLieExtension.extendLieHom_tmul]
      simp only [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply, map_smul]
      congr 1
      exact pointPullback_plotSmoothDifferential hH hG f X u
    | add U V hU hV => simp only [map_add, LinearMap.add_apply, hU, hV]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

end Langlands.Automorphic.GroupSchemeFunctions
