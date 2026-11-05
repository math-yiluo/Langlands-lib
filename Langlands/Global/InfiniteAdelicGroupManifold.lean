import Langlands.Geometry.Manifold.FinitePi
import Langlands.Global.InfinitePlaceGroupManifold
import Langlands.Global.InfiniteAdelicGroupCoordinateSmooth

/-! # The manifold and Lie group of actual infinite adelic group points -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ}

/-- The real normed model formed from the actual completion coordinate spaces. -/
abbrev smoothModel (d : ℕ) :=
  (v : InfinitePlace F) → Fin d → v.Completion

/-- Product charts of the specified local completion manifolds. -/
@[instance_reducible]
def productChartedSpace (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (smoothModel F d)
      ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  exact finitePiChartedSpace
    (fun v : InfinitePlace F => Fin d → v.Completion)
    (fun v : InfinitePlace F => InfinitePlaceGroupPoints F G v)

/-- The finite completion product is a manifold for precisely these charts. -/
theorem productIsManifold (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := productChartedSpace F G hsmooth
    IsManifold 𝓘(ℝ, smoothModel F d) ∞
      ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothIsManifold F G v hsmooth
  exact finitePiIsManifold (𝕜 := ℝ)
    (fun v : InfinitePlace F => Fin d → v.Completion)
    (fun v : InfinitePlace F => InfinitePlaceGroupPoints F G v) ∞

/-- Pull the finite product atlas back through the actual completion homeomorphism. -/
@[instance_reducible]
def smoothChartedSpace (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (smoothModel F d) (InfiniteAdelicGroupPoints F G) := by
  letI := productChartedSpace F G hsmooth
  exact pullbackChartedSpace (H := smoothModel F d) (completions F G).toHomeomorph

/-- The original infinite adelic evaluation topology supports the constructed manifold. -/
theorem smoothIsManifold (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := productChartedSpace F G hsmooth
  let := productIsManifold F G hsmooth
  exact pullbackIsManifold 𝓘(ℝ, smoothModel F d) ∞ (completions F G).toHomeomorph

/-- The actual group decomposition is a diffeomorphism for the specified atlases. -/
def completionsDiffeomorph (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := productChartedSpace F G hsmooth
    letI := smoothChartedSpace F G hsmooth
    Diffeomorph 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d)
      (InfiniteAdelicGroupPoints F G)
      ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) ∞ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := productChartedSpace F G hsmooth
  exact pullbackDiffeomorph 𝓘(ℝ, smoothModel F d) ∞ (completions F G).toHomeomorph

theorem completionsDiffeomorph_toEquiv (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := productChartedSpace F G hsmooth
    let := smoothChartedSpace F G hsmooth
    (completionsDiffeomorph F G hsmooth).toEquiv = (completions F G).toEquiv := rfl

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Manifold smoothness into the original infinite adelic group is componentwise. -/
theorem contMDiff_iff_places (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → InfiniteAdelicGroupPoints F G) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
    let := smoothChartedSpace F G hsmooth
    ContMDiff I 𝓘(ℝ, smoothModel F d) ∞ p ↔
      ∀ v : InfinitePlace F, ContMDiff I 𝓘(ℝ, Fin d → v.Completion) ∞
        (fun x => atPlace F G v (p x)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := productChartedSpace F G hsmooth
  exact (contMDiff_pullback_iff 𝓘(ℝ, smoothModel F d) ∞ I
    (completions F G).toHomeomorph p).trans
      (contMDiff_finitePi_iff
        (fun v : InfinitePlace F => Fin d → v.Completion)
        (fun v : InfinitePlace F => InfinitePlaceGroupPoints F G v)
        I ∞ (fun x => completions F G (p x)))

/-- The constructed manifold detects exactly the original mixed regular-coordinate
smoothness, with no manifold premise on the parameter space. -/
theorem contMDiff_iff_coordinateSmooth (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → InfiniteAdelicGroupPoints F G) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    ContMDiff I 𝓘(ℝ, smoothModel F d) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  apply (contMDiff_iff_places F G I hsmooth p).trans
  apply Iff.trans ?_ (coordinateSmooth_iff_completions F G I p).symm
  constructor
  · intro hp
    constructor
    · intro vr
      exact (InfinitePlaceGroupPoints.contMDiff_iff_realCoordinates
        F G vr.1 I vr.2 hsmooth _).mp (hp vr.1)
    · intro vc
      exact (InfinitePlaceGroupPoints.contMDiff_iff_complexCoordinates
        F G vc.1 I vc.2 hsmooth _).mp (hp vc.1)
  · intro hp v
    rcases isReal_or_isComplex v with hv | hv
    · exact (InfinitePlaceGroupPoints.contMDiff_iff_realCoordinates
        F G v I hv hsmooth _).mpr (hp.1 ⟨v, hv⟩)
    · exact (InfinitePlaceGroupPoints.contMDiff_iff_complexCoordinates
        F G v I hv hsmooth _).mpr (hp.2 ⟨v, hv⟩)

/-- The original infinite adelic multiplication and inverse are smooth for the
constructed charts and original evaluation topology. -/
theorem smoothLieGroup (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    LieGroup 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply (contMDiff_iff_coordinateSmooth F G
      (𝓘(ℝ, smoothModel F d).prod 𝓘(ℝ, smoothModel F d)) hsmooth _).mpr
    apply GroupScheme.CoordinateSmooth.mul G (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    · exact (contMDiff_iff_coordinateSmooth F G
        (𝓘(ℝ, smoothModel F d).prod 𝓘(ℝ, smoothModel F d)) hsmooth _).mp contMDiff_fst
    · exact (contMDiff_iff_coordinateSmooth F G
        (𝓘(ℝ, smoothModel F d).prod 𝓘(ℝ, smoothModel F d)) hsmooth _).mp contMDiff_snd
  · apply (contMDiff_iff_coordinateSmooth F G 𝓘(ℝ, smoothModel F d) hsmooth _).mpr
    exact ((contMDiff_iff_coordinateSmooth F G
      𝓘(ℝ, smoothModel F d) hsmooth _).mp contMDiff_id).inv

/-- Every actual completion projection is smooth. -/
theorem contMDiff_atPlace (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
    let := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, Fin d → v.Completion) ∞
      (atPlace F G v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact (contMDiff_iff_places F G 𝓘(ℝ, smoothModel F d) hsmooth id).mp contMDiff_id v

/-- Assembly from the completion product is the smooth inverse of the actual
completion decomposition. -/
theorem contMDiff_assemble (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := productChartedSpace F G hsmooth
    let := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d) ∞
      (assemble F G) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := productChartedSpace F G hsmooth
  let := smoothChartedSpace F G hsmooth
  exact (completionsDiffeomorph F G hsmooth).symm.contMDiff

/-- Each original regular-function evaluation is smooth in the specified mixed
real/complex coordinates. -/
theorem contMDiff_mixedEvaluation (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (a : Γ(G.X.left, ⊤)) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, mixedEmbedding.mixedSpace F) ∞
      (fun x : InfiniteAdelicGroupPoints F G =>
        InfiniteAdeleRing.ringEquiv_mixedSpace F
          (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact ((contMDiff_iff_coordinateSmooth F G
    𝓘(ℝ, smoothModel F d) hsmooth id).mp contMDiff_id) a

/-- Each original regular-function value at an actual completion is smooth. -/
theorem contMDiff_completionEvaluation (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) (a : Γ(G.X.left, ⊤)) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
      (fun x : InfiniteAdelicGroupPoints F G =>
        G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  have h := (InfinitePlaceGroupPoints.contMDiff_iff_coordinateSmooth
    F G v 𝓘(ℝ, smoothModel F d) hsmooth (atPlace F G v)).mp
      (contMDiff_atPlace F G hsmooth v) a
  exact h.congr (fun x => (atPlace_evaluation F G x a v).symm)

end Langlands.Global.InfiniteAdelicGroupPoints
