import Langlands.Geometry.Analytic.RecognizedOpenImageCover
import Langlands.Geometry.Analytic.RecognizedDomainMapCompatibility
import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement

/-! # Complete finite affine models over a recognized target cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace RecognizedOpenImageCover

variable {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {R : B.atlas.saturatedAtlas.RecognizedSubset} {U : Set C.space}
  (c : g.RecognizedOpenImageCover R U)

/-- The chart identity of a local model supplies exactly the ambient
admissibility needed by the canonical full-recognition bounded map. -/
theorem image_subset_target (i : Fin c.cover.size) :
    g.baseMap '' (R.chart '' (c.cover.obj i).locus) ⊆ (c.target i).locus := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := (c.cover.obj i).represents.2.1.symm ▸ hx
  exact (c.target i).range_chart.subset
    ⟨_, (c.chart_comm i y).trans (congrArg (fun z => g.baseMap (R.chart z)) hy)⟩

/-- Use the actual g pair pullback on each full domain, transported through
constructed recognition equivalences, retaining all algebra coefficients. -/
def canonicalPullback (i : Fin c.cover.size) :
    BoundedAlgHom K (c.target i).algebra (c.cover.obj i).algebra :=
  g.domainRecognitionPullback R (c.cover.obj i) (c.target i) (c.image_subset_target i)

theorem canonicalPullback_chart (i : Fin c.cover.size)
    (x : BanachSpectrum (c.cover.obj i).algebra) :
    (c.target i).chart (BanachSpectrum.comap (c.canonicalPullback i).toBoundedRingHom x) =
      g.baseMap (R.chart ((c.cover.obj i).spectrumMap x)) :=
  g.domainRecognitionPullback_chart R (c.cover.obj i) (c.target i) (c.image_subset_target i) x

/-- Canonical local maps satisfy the entire coefficient-test target-chart
change on every actual full overlap of two cover members. -/
theorem canonicalPullback_overlap (i j : Fin c.cover.size)
    (E : Domain K R.algebra) (r : E ⟶ c.cover.obj i) (s : E ⟶ c.cover.obj j) :
    C.fullRecognitionPresentation.atlas.IsMapChartChange (c.target i) (c.target j) E.algebra
      (r.restriction.comp (c.canonicalPullback i))
      (s.restriction.comp (c.canonicalPullback j)) :=
  g.domainRecognitionPullback_overlap R r s (c.target i) (c.target j)
    (c.image_subset_target i) (c.image_subset_target j)

end RecognizedOpenImageCover

/-- Local finite preimages and their actual second-source full-domain
cover, ready for effective finite algebra descent. -/
structure FiniteOpenBaseChangeModels
    (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
    (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : Set A.space) (U : Set C.space)
    (R : B.atlas.saturatedAtlas.RecognizedSubset) where
  rightCover : g.RecognizedOpenImageCover R U
  left : Fin rightCover.cover.size → A.atlas.saturatedAtlas.RecognizedSubset
  left_admissible : ∀ i, f.baseMap '' range (left i).chart ⊆ range (rightCover.target i).chart
  left_locus : ∀ i, (left i).locus = V ∩ f.baseMap ⁻¹' (rightCover.target i).locus
  left_finite : ∀ i,
    (f.fullRecognitionPairs.pullback (left i) (rightCover.target i) (left_admissible i)).IsFiniteBanach

/-- Finite-over data supplies every entire local preimage over the actual
finite target cover; no global descended parent is supplied or inferred. -/
def finiteOpenBaseChangeModels
    (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
    (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
    {V : Set A.space} {U : Set C.space} (hf : f.IsFiniteOver V U) (hU : IsOpen U)
    (R : B.atlas.saturatedAtlas.RecognizedSubset) (hR : g.baseMap '' R.locus ⊆ U) :
    FiniteOpenBaseChangeModels f g V U R := by
  classical
  let c := g.recognizedOpenImageCover R U hU hR
  choose P h hP hfinite using fun i : Fin c.cover.size => hf.2 (c.target i) (c.target_subset i)
  exact ⟨c, P, h, hP, hfinite⟩

namespace FiniteOpenBaseChangeModels

variable {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R) (i : Fin M.rightCover.cover.size)

/-- The original complete bounded finite left map. -/
def leftBase : BoundedAlgHom K (M.rightCover.target i).algebra (M.left i).algebra :=
  f.fullRecognitionPairs.pullback (M.left i) (M.rightCover.target i) (M.left_admissible i)

/-- The actual finite base-change algebra, using canonical complete right data. -/
def algebra : PresentedAffinoidAlgebra K :=
  AffinoidPushout.algebra (M.leftBase i) (M.rightCover.canonicalPullback i)

/-- The actual first closed-quotient leg retains every original coefficient. -/
def leftMap : BoundedAlgHom K (M.left i).algebra (M.algebra i) :=
  AffinoidPushout.leftMap (M.leftBase i) (M.rightCover.canonicalPullback i)

/-- The actual finite map from the cover member into its local model. -/
def rightMap : BoundedAlgHom K (M.rightCover.cover.obj i).algebra (M.algebra i) :=
  AffinoidPushout.rightMap (M.leftBase i) (M.rightCover.canonicalPullback i)

theorem condition : (M.leftMap i).comp (M.leftBase i) =
    (M.rightMap i).comp (M.rightCover.canonicalPullback i) :=
  AffinoidPushout.condition _ _

theorem rightMap_isFiniteBanach (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    (M.rightMap i).IsFiniteBanach :=
  hpush _ _ _ (M.leftBase i) (M.rightCover.canonicalPullback i) (M.left_finite i)

/-- Pointwise etaleness at the actual first image transfers to the actual
changed-base leg under the full finite tensor comparison. -/
theorem rightMap_isEtaleAtPoint
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (x : BanachSpectrum (M.algebra i))
    (hx : (M.leftBase i).IsEtaleAtPoint
      (BanachSpectrum.comap (M.leftMap i).toBoundedRingHom x)) :
    (M.rightMap i).IsEtaleAtPoint x :=
  AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison
    (M.leftBase i) (M.rightCover.canonicalPullback i)
    (htensor _ _ _ _ _ (M.left_finite i)) (M.left_finite i).finite.finiteType x hx

/-- Both actual local model projections have the same original ambient
image, by the full bounded pushout equation. -/
theorem ambient_condition (x : BanachSpectrum (M.algebra i)) :
    f.baseMap ((M.left i).chart (BanachSpectrum.comap (M.leftMap i).toBoundedRingHom x)) =
      g.baseMap (R.chart ((M.rightCover.cover.obj i).spectrumMap
        (BanachSpectrum.comap (M.rightMap i).toBoundedRingHom x))) := by
  have he : BanachSpectrum.comap ((M.leftMap i).comp (M.leftBase i)).toBoundedRingHom x =
      BanachSpectrum.comap ((M.rightMap i).comp (M.rightCover.canonicalPullback i)).toBoundedRingHom x :=
    congrArg (fun q : BoundedAlgHom K (M.rightCover.target i).algebra (M.algebra i) =>
      BanachSpectrum.comap q.toBoundedRingHom x) (M.condition i)
  exact (f.fullRecognitionPairs.chart_comm (M.left i) (M.rightCover.target i)
    (M.left_admissible i) (BanachSpectrum.comap (M.leftMap i).toBoundedRingHom x)).symm.trans
      ((congrArg (M.rightCover.target i).chart he).trans
        (M.rightCover.canonicalPullback_chart i
          (BanachSpectrum.comap (M.rightMap i).toBoundedRingHom x)))

/-- The local first projection lies in precisely the prescribed finite
source neighborhood, with no assumption of affinoid neighborhoods. -/
theorem leftPoint_mem (x : BanachSpectrum (M.algebra i)) :
    (M.left i).chart (BanachSpectrum.comap (M.leftMap i).toBoundedRingHom x) ∈ V :=
  ((M.left_locus i).subset
    ((M.left i).range_chart.subset ⟨_, rfl⟩)).1

end FiniteOpenBaseChangeModels

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
