import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Automorphic.GroupSchemePlotSmooth

/-! # The specified adelic manifold and the existing smooth slice spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.InfiniteAdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- The existing all-family predicate is exactly ordinary real smoothness
for the specified actual infinite adelic manifold. -/
theorem isPlotSmooth_iff_contMDiff
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (f : InfiniteAdelicGroupPoints F G → ℂ) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    G.IsPlotSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom f ↔
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ f := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  constructor
  · intro hf
    have hp := (contMDiff_iff_coordinateSmooth F G
      𝓘(ℝ, smoothModel F d) hsmooth
      (id : InfiniteAdelicGroupPoints F G → InfiniteAdelicGroupPoints F G)).mp contMDiff_id
    exact hf (smoothModel F d) (InfiniteAdelicGroupPoints F G) id hp
  · intro hf E _ _ M _ _ p hp
    exact hf.comp ((contMDiff_iff_coordinateSmooth F G 𝓘(ℝ, E) hsmooth p).mpr hp)

/-- The ordinary smooth-function submodule on the original point carrier. -/
def manifoldSmoothFunctions (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    Submodule ℂ (InfiniteAdelicGroupPoints F G → ℂ) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact
    { carrier := {f | ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ f}
      zero_mem' := contMDiff_const
      add_mem' hf hg := hf.add hg
      smul_mem' c f hf :=
        (((ContinuousLinearMap.mul ℝ ℂ) c).contDiff.contMDiff).comp hf }

/-- The two submodules contain exactly the same original functions. -/
theorem plotSmoothFunctions_eq_manifoldSmoothFunctions
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom =
        manifoldSmoothFunctions F G hsmooth := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  ext f
  exact isPlotSmooth_iff_contMDiff F G hsmooth f

/-- Any two supplied algebraic dimensions give the same smooth-function
submodule, without identifying independently selected charted spaces. -/
theorem manifoldSmoothFunctions_eq {d' : ℕ}
    (h : SmoothOfRelativeDimension d G.X.hom)
    (h' : SmoothOfRelativeDimension d' G.X.hom) :
    manifoldSmoothFunctions F G h = manifoldSmoothFunctions F G h' :=
  (plotSmoothFunctions_eq_manifoldSmoothFunctions F G h).symm.trans
    (plotSmoothFunctions_eq_manifoldSmoothFunctions F G h')

/-- Connected reductivity suffices for the ordinary manifold interpretation. -/
theorem reductive_isPlotSmooth_iff_contMDiff
    (hG : GroupScheme.IsConnectedReductive G)
    (f : InfiniteAdelicGroupPoints F G → ℂ) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := reductiveChartedSpace F G hG
    G.IsPlotSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom f ↔
      ContMDiff 𝓘(ℝ, smoothModel F hG.smoothDimension) 𝓘(ℝ, ℂ) ∞ f :=
  isPlotSmooth_iff_contMDiff F G hG.smoothDimension_spec f

end Langlands.Global.InfiniteAdelicGroupPoints

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- Infinite smoothness in the existing subrepresentation means ordinary
smoothness of every actual infinite slice in the specified manifold. -/
theorem mem_infinitePlotSmoothSubrepresentation_iff_contMDiff
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (f : ContinuousRationalFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    f ∈ infinitePlotSmoothSubrepresentation F G ↔
      ∀ b : FiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞
          (infiniteSlice F G b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  exact (mem_infinitePlotSmoothSubrepresentation F G f).trans
    (forall_congr' fun b => InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff
      F G hsmooth (infiniteSlice F G b f))

/-- The slice-regular space uses actual infinite manifold smoothness and
the original local constancy condition on each finite slice. -/
theorem mem_plotSmoothSubrepresentation_iff_contMDiff
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (f : ContinuousRationalFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    f ∈ plotSmoothSubrepresentation F G ↔
      (∀ b : FiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞
          (infiniteSlice F G b f)) ∧
      f ∈ finiteLocallyConstantSubrepresentation F G := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  change (f ∈ infinitePlotSmoothSubrepresentation F G ∧
    f ∈ finiteLocallyConstantSubrepresentation F G) ↔ _
  exact and_congr_left' (mem_infinitePlotSmoothSubrepresentation_iff_contMDiff F G hsmooth f)

/-- The common-open-stabilizer space retains that finite condition verbatim. -/
theorem mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (f : ContinuousRationalFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    f ∈ finitePlotSmoothRationalSubrepresentation F G ↔
      (∀ b : FiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞
          (infiniteSlice F G b f)) ∧
      f ∈ finiteSmoothSubrepresentation F G := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  change (f ∈ infinitePlotSmoothSubrepresentation F G ∧
    f ∈ finiteSmoothSubrepresentation F G) ↔ _
  exact and_congr_left' (mem_infinitePlotSmoothSubrepresentation_iff_contMDiff F G hsmooth f)

/-- Ordinary smooth slices follow directly from the original
connected-reductive predicate. -/
theorem reductive_mem_infinitePlotSmoothSubrepresentation_iff_contMDiff
    (hG : GroupScheme.IsConnectedReductive G)
    (f : ContinuousRationalFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
    f ∈ infinitePlotSmoothSubrepresentation F G ↔
      ∀ b : FiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)
          𝓘(ℝ, ℂ) ∞ (infiniteSlice F G b f) :=
  mem_infinitePlotSmoothSubrepresentation_iff_contMDiff F G hG.smoothDimension_spec f

end Langlands.Automorphic.GroupSchemeFunctions
