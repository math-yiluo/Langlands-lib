import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationStatement
import Langlands.Global.AdelicInducedConvolutionFiniteSpanReduction
import Langlands.Global.AdelicInducedConvolutionLeviDifferential

/-! # A common center ideal for the integrated induced action -/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- Pointwise adjoint invariance of the ambient center and an unnormalized Levi center
comparison at the identity give one annihilator for all parameters of the induced convolution. -/
def InducedConvolutionUniformCenterReductionStatement : Prop :=
  AdelicEnvelopingCenterConjugationStatement.{0} →
  (∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [IsAffine M.X.left]
    (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P),
    IsConnectedReductive G → IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsIso (subgroupMultiplication l iU) →
    ∀ {d e : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (hM : SmoothOfRelativeDimension e M.X.hom)
      (hcG : AdelicDifferentialCommutator F G hG) (hcM : AdelicDifferentialCommutator F M hM),
      ∃ (restrict : InfinitePlotSmoothFunctions F G →ₗ[ℂ] InfinitePlotSmoothFunctions F M)
        (c : AdelicEnvelopingCenter F G hG → AdelicEnvelopingCenter F M hM),
        (∀ (f : InfinitePlotSmoothFunctions F G) (m : InfiniteAdelicGroupPoints F M),
          (restrict f).val m =
            f.val (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F (InfiniteAdeleRing F)) m)) ∧
        ∀ f : InfinitePlotSmoothFunctions F G,
          (∀ (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G),
            f.val (U.affinePointsTarget (iU ≫ p) (CommAlgCat.of F (InfiniteAdeleRing F)) u * x) =
              f.val x) →
          ∀ z, restrict (plotSmoothCenterAction F G hG hcG z f) =
            plotSmoothCenterAction F M hM hcM (c z) (restrict f)) →
    InducedConvolutionUniformCenterIdealStatement

set_option maxHeartbeats 1200000 in
/-- The input center ideal works for the whole family. Use one fixed Levi comparison
and the transfer of Levi differential annihilators through convolution. -/
theorem inducedConvolutionUniformCenterReduction : InducedConvolutionUniformCenterReductionStatement := by
  intro hAd hRestr F _ _ G P M U _ _ _ _ _ _ p _ iU l hG hp hU hl hiso K hK _ d hsmooth hcalc
    φ v hφ hsupp hv hvInv hvCenter
  let : IsClosedImmersion iU.hom.hom.left := hU.1.isClosedSubgroup
  let : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  let hM := hl.isConnectedReductive.smoothDimension_spec
  let hcM := adelicDifferentialCommutator_of_smooth F M hM
  let A := CommAlgCat.of F (InfiniteAdeleRing F)
  let unip := U.affinePointsTarget (iU ≫ p) A
  let levi := M.affinePointsTarget (l ≫ p) A
  let ambient := plotSmoothCenterAction F G hsmooth hcalc
  let onLevi := plotSmoothCenterAction F M hM hcM
  obtain ⟨restrictBase, c, hEval, hc⟩ :=
    hRestr F G P M U p iU l hG hp hU hl hiso hsmooth hM hcalc hcM
  let restrict (a : InfiniteAdelicGroupPoints F G) :=
    restrictBase.comp (infiniteSliceRightTranslation a)
  have hRestrictEval (a : InfiniteAdelicGroupPoints F G) (f : InfinitePlotSmoothFunctions F G)
      (m : InfiniteAdelicGroupPoints F M) :
      (restrict a f).val m = f.val (levi m * a) :=
    hEval (infiniteSliceRightTranslation a f) m
  have hcompare (a : InfiniteAdelicGroupPoints F G) (f : InfinitePlotSmoothFunctions F G)
      (hf : ∀ (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G),
        f.val (unip u * x) = f.val x) (z : AdelicEnvelopingCenter F G hsmooth) :
      restrict a (ambient z f) = onLevi (c z) (restrict a f) := by
    have hcomm : infiniteSliceRightTranslation a (ambient z f) =
        ambient z (infiniteSliceRightTranslation a f) := by
      change infiniteSliceRightTranslation a (plotSmoothEnvelopingAction F G hsmooth hcalc z.val f) =
        plotSmoothEnvelopingAction F G hsmooth hcalc z.val (infiniteSliceRightTranslation a f)
      rw [infiniteSliceRightTranslationCovariance F G hsmooth hcalc a z.val f,
        hAd F G hsmooth hG a z.val z.property]
    have hinv (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G) :
        (infiniteSliceRightTranslation a f).val (unip u * x) =
          (infiniteSliceRightTranslation a f).val x := by
      simp only [infiniteSliceRightTranslation_apply, mul_assoc, hf]
    change restrictBase (infiniteSliceRightTranslation a (ambient z f)) =
      onLevi (c z) (restrictBase (infiniteSliceRightTranslation a f))
    rw [hcomm]
    exact hc _ hinv z
  have hSliceInv (f : AdelicGroupPoints F G → ℂ)
      (hf : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) f)
      (b : FiniteAdelicGroupPoints F G) (u : InfiniteAdelicGroupPoints F U)
      (x : InfiniteAdelicGroupPoints F G) :
      functionInfiniteSlice F G f b (unip u * x) = functionInfiniteSlice F G f b x := by
    have he := hf (map F U G (iU ≫ p) (ofInfinite F U u)) ⟨ofInfinite F U u, rfl⟩ (pair F G x b)
    rw [map_ofInfinite, ofInfinite_eq_pair, pair_mul, one_mul] at he
    exact he
  have hSliceEq (f : AdelicGroupPoints F G → ℂ) (a : InfiniteAdelicGroupPoints F G)
      (b : FiniteAdelicGroupPoints F G) (hf : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G) :
      (restrict a ⟨functionInfiniteSlice F G f b, hf⟩).val = infiniteLeviSlice p l f (pair F G a b) := by
    funext m
    rw [hRestrictEval a ⟨functionInfiniteSlice F G f b, hf⟩ m]
    change f (pair F G (levi m * a) b) = f (map F M G (l ≫ p) (ofInfinite F M m) * pair F G a b)
    rw [map_ofInfinite, ofInfinite_eq_pair, pair_mul, one_mul]
  obtain ⟨J, hJ, hvAnn⟩ := hvCenter
  refine ⟨J, hJ, ?_⟩
  intro lam z hz b hb
  have hvLevi (g : AdelicGroupPoints F G) (hg : infiniteLeviSlice p l v g ∈ InfinitePlotSmoothFunctions F M) :
      plotSmoothEnvelopingAction F M hM hcM (c z).val ⟨infiniteLeviSlice p l v g, hg⟩ = 0 := by
    let a := infinite F G g
    let b₀ := finite F G g
    let vSlice : InfinitePlotSmoothFunctions F G := ⟨functionInfiniteSlice F G v b₀, hv.2.1 b₀⟩
    have he := hSliceEq v a b₀ (hv.2.1 b₀)
    change (restrict a vSlice).val = infiniteLeviSlice p l v (pair F G (infinite F G g) (finite F G g)) at he
    rw [pair_projections] at he
    have hsub : restrict a vSlice = ⟨infiniteLeviSlice p l v g, hg⟩ := Subtype.ext he
    change onLevi (c z) ⟨infiniteLeviSlice p l v g, hg⟩ = 0
    rw [← hsub, ← hcompare a vSlice (hSliceInv v hvInv b₀) z,
      hvAnn z hz b₀ (hv.2.1 b₀), map_zero]
  let w := hK.inducedConvolution lam φ v
  have hwInv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) w := by
    rintro _ ⟨u, rfl⟩ g
    have he (y : AdelicGroupPoints F G) : v (map F P G p (map F U P iU u) * y) = 1 * v y := by
      rw [← map_comp_apply_of_hom, one_mul]
      exact hvInv _ ⟨u, rfl⟩ y
    change w (map F U G (iU ≫ p) u * g) = w g
    rw [map_comp_apply_of_hom]
    exact (hK.integral_translate_left_equivariant φ v lam _ 1 he g).trans (one_mul _)
  let wSlice : InfinitePlotSmoothFunctions F G := ⟨functionInfiniteSlice F G w b, hb⟩
  apply Subtype.ext
  funext a
  have he : (restrict a wSlice).val = infiniteLeviSlice p l w (pair F G a b) := hSliceEq w a b hb
  have hplot : infiniteLeviSlice p l w (pair F G a b) ∈ InfinitePlotSmoothFunctions F M :=
    he ▸ (restrict a wSlice).property
  have hsub : restrict a wSlice = ⟨infiniteLeviSlice p l w (pair F G a b), hplot⟩ := Subtype.ext he
  have hzero : onLevi (c z) (restrict a wSlice) = 0 := by
    rw [hsub]
    exact inducedConvolutionLeviAnnihilator F G P M p l K hK hsmooth hM hcM (c z).val φ v
      hφ hsupp hv hvLevi lam (pair F G a b) hplot
  have hAnn := hcompare a wSlice (hSliceInv w hwInv b) z
  rw [hzero] at hAnn
  have hpoint := congrArg (fun f : InfinitePlotSmoothFunctions F M => f.val 1) hAnn
  change (restrict a (ambient z wSlice)).val 1 = 0 at hpoint
  rw [hRestrictEval, map_one, one_mul] at hpoint
  exact hpoint

end Langlands.Global
