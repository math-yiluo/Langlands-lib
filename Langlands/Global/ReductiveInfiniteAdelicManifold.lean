import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Infinite adelic manifolds from connected reductivity -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme.IsConnectedReductive

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Connected reductivity supplies constant relative dimension, with no
dimension or differential-rank premise. -/
theorem exists_smoothOfRelativeDimension (hG : IsConnectedReductive G) :
    ∃ d : ℕ, SmoothOfRelativeDimension d G.X.hom :=
  Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG.smooth hG.connectedSpace

/-- A fixed algebraic chart dimension, chosen from the proved existence. -/
def smoothDimension (hG : IsConnectedReductive G) : ℕ :=
  Nat.find hG.exists_smoothOfRelativeDimension

theorem smoothDimension_spec (hG : IsConnectedReductive G) :
    SmoothOfRelativeDimension hG.smoothDimension G.X.hom :=
  Nat.find_spec hG.exists_smoothOfRelativeDimension

/-- Affineness of the actual underlying scheme follows from reductivity. -/
theorem affineScheme (hG : IsConnectedReductive G) : IsAffine G.X.left := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact isAffine_of_isAffineHom G.X.hom

end Langlands.GroupScheme.IsConnectedReductive

namespace Langlands.Global.InfinitePlaceGroupPoints

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (hG : GroupScheme.IsConnectedReductive G) (v : InfinitePlace F)

/-- The named completion atlas now requires only connected reductivity. -/
@[instance_reducible]
def reductiveChartedSpace :
    letI := hG.affineScheme
    ChartedSpace (Fin hG.smoothDimension → v.Completion)
      (InfinitePlaceGroupPoints F G v) := by
  letI := hG.affineScheme
  exact smoothChartedSpace F G v hG.smoothDimension_spec

theorem reductiveIsManifold :
    letI := hG.affineScheme
    letI := completionRCLike F v
    letI := reductiveChartedSpace F G hG v
    IsManifold 𝓘(ℝ, Fin hG.smoothDimension → v.Completion) ∞
      (InfinitePlaceGroupPoints F G v) := by
  let := hG.affineScheme
  let := completionRCLike F v
  exact smoothIsManifold F G v hG.smoothDimension_spec

/-- Original local multiplication and inversion are smooth with no additional
analytic or dimension hypothesis. -/
theorem reductiveLieGroup :
    letI := hG.affineScheme
    letI := completionRCLike F v
    letI := reductiveChartedSpace F G hG v
    LieGroup 𝓘(ℝ, Fin hG.smoothDimension → v.Completion) ∞
      (InfinitePlaceGroupPoints F G v) := by
  let := hG.affineScheme
  let := completionRCLike F v
  exact smoothLieGroup F G v hG.smoothDimension_spec

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

theorem reductive_contMDiff_iff_coordinateSmooth
    (p : M → InfinitePlaceGroupPoints F G v) :
    letI := hG.affineScheme
    letI := completionRCLike F v
    letI := reductiveChartedSpace F G hG v
    ContMDiff I 𝓘(ℝ, Fin hG.smoothDimension → v.Completion) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F v.Completion)
        (RingHom.id v.Completion) I p := by
  let := hG.affineScheme
  let := completionRCLike F v
  exact contMDiff_iff_coordinateSmooth F G v I hG.smoothDimension_spec p

end Langlands.Global.InfinitePlaceGroupPoints

namespace Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (hG : GroupScheme.IsConnectedReductive G)

/-- The actual infinite adelic group atlas derived from connected reductivity. -/
@[instance_reducible]
def reductiveChartedSpace :
    letI := hG.affineScheme
    ChartedSpace (smoothModel F hG.smoothDimension) (InfiniteAdelicGroupPoints F G) := by
  letI := hG.affineScheme
  exact smoothChartedSpace F G hG.smoothDimension_spec

theorem reductiveIsManifold :
    letI := hG.affineScheme
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    IsManifold 𝓘(ℝ, smoothModel F hG.smoothDimension) ∞
      (InfiniteAdelicGroupPoints F G) := by
  let := hG.affineScheme
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact smoothIsManifold F G hG.smoothDimension_spec

/-- The existing infinite adelic multiplication and inversion form a real
Lie group directly from the original algebraic predicate. -/
theorem reductiveLieGroup :
    letI := hG.affineScheme
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    LieGroup 𝓘(ℝ, smoothModel F hG.smoothDimension) ∞
      (InfiniteAdelicGroupPoints F G) := by
  let := hG.affineScheme
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact smoothLieGroup F G hG.smoothDimension_spec

/-- The original completion decomposition, with its specified product atlas. -/
def reductiveCompletionsDiffeomorph :
    letI := hG.affineScheme
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := productChartedSpace F G hG.smoothDimension_spec
    letI := reductiveChartedSpace F G hG
    Diffeomorph 𝓘(ℝ, smoothModel F hG.smoothDimension)
      𝓘(ℝ, smoothModel F hG.smoothDimension)
      (InfiniteAdelicGroupPoints F G)
      ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) ∞ := by
  letI := hG.affineScheme
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact completionsDiffeomorph F G hG.smoothDimension_spec

theorem reductiveCompletionsDiffeomorph_toEquiv :
    letI := hG.affineScheme
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := productChartedSpace F G hG.smoothDimension_spec
    letI := reductiveChartedSpace F G hG
    (reductiveCompletionsDiffeomorph F G hG).toEquiv =
      (completions F G).toEquiv := rfl

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Smooth families in the reductive atlas are precisely the original mixed
regular-coordinate-smooth families, even for an arbitrary charted source. -/
theorem reductive_contMDiff_iff_coordinateSmooth
    (p : M → InfiniteAdelicGroupPoints F G) :
    letI := hG.affineScheme
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    ContMDiff I 𝓘(ℝ, smoothModel F hG.smoothDimension) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p := by
  let := hG.affineScheme
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact contMDiff_iff_coordinateSmooth F G I hG.smoothDimension_spec p

end Langlands.Global.InfiniteAdelicGroupPoints
