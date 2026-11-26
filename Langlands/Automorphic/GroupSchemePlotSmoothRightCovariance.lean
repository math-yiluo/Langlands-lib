import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof

/-! # Right-translation covariance on infinite adelic plot-smooth functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped Classical CategoryTheory.MonObj ContDiff Manifold TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

section Derivative

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "A∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "coordinates" => RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F)
local notation "R" => G.plotSmoothRightAction A∞ coordinates

private theorem plotSmoothDifferential_rightTranslation (g : G∞) (f : InfinitePlotSmoothFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ X : smoothModel F d, R g (plotSmoothDifferential F G hsmooth X f) =
      plotSmoothDifferential F G hsmooth (adelicTangentConjugation F G hsmooth g X) (R g f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  intro X
  apply Subtype.ext
  funext x
  exact groupDirectionalValue_rightTranslation _ g X
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property) x

end Derivative

/-- On the infinite adelic plot-smooth space, right translation carries each enveloping
operator to the operator given by the adjoint image. -/
def AdelicPlotSmoothEnvelopingRightCovarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (g : InfiniteAdelicGroupPoints F G) (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : InfinitePlotSmoothFunctions F G),
      let R := G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      R g (plotSmoothEnvelopingAction F G hsmooth hcalc a f) =
        plotSmoothEnvelopingAction F G hsmooth hcalc (adelicEnvelopingConjugation F G hsmooth g a)
          (R g f)

theorem adelicPlotSmoothEnvelopingRightCovariance :
    AdelicPlotSmoothEnvelopingRightCovarianceStatement.{u} := by
  intro F _ _ G _ d hsmooth hcalc g a f R
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  let act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let adj := adelicEnvelopingConjugation F G hsmooth g
  change R g (act a f) = act (adj a) (R g f)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap z =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply,
      Module.End.one_apply]
  | «ι» Z =>
    change R g (act (UniversalEnvelopingAlgebra.ι ℂ Z) f) =
      act (adj (UniversalEnvelopingAlgebra.ι ℂ Z)) (R g f)
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      dsimp only [act, adj]
      rw [adelicEnvelopingConjugation_ι_tmul, plotSmoothEnvelopingAction_generator,
        plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul,
        complexPlotSmoothLieAction_tmul]
      simp only [LinearMap.smul_apply, map_smul]
      rw [plotSmoothDifferential_rightTranslation F G hsmooth]
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply]
      rw [hX, hY]
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hx, hy]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]

/-- Right translation commutes with each center operator for a connected reductive group. -/
theorem plotSmoothCenterAction_rightTranslation
    (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (g : InfiniteAdelicGroupPoints F G) (z : AdelicEnvelopingCenter F G hsmooth)
    (f : InfinitePlotSmoothFunctions F G) :
    let R := G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    R g (plotSmoothCenterAction F G hsmooth hcalc z f) =
      plotSmoothCenterAction F G hsmooth hcalc z (R g f) := by
  intro R
  have h := adelicPlotSmoothEnvelopingRightCovariance F G hsmooth hcalc g z.val f
  rw [adelicEnvelopingCenterConjugation F G hsmooth hG g z.val z.property] at h
  exact h

end Langlands.Automorphic.GroupSchemeFunctions
