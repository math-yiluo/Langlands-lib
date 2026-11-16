import Langlands.Geometry.Analytic.FullRecognitionFiniteCharacterLifting
import Langlands.Geometry.Analytic.FieldPointChartExtension
import Langlands.Geometry.Analytic.EtaleGeometricPointImageTransport

/-! # Prescribed full field points for locally finite maps -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace FieldPoint

/-- Evaluation of the image in full recognition can use any recognized
source chart through the point that maps into the given target chart. -/
theorem map_toFullRecognitionTarget_eval
    (q : FieldPoint L A.saturatedPresentation)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hVW : g.baseMap '' range V.chart ⊆ range W.chart)
    (hV : q.point ∈ range V.chart)
    (hW : g.baseMap q.point ∈ range W.chart) :
    (q.map g.toFullRecognitionTarget A.atlas.saturatedAtlas_hasAllLocalDomains).eval W hW =
      ((q.map A.localDomainToFullRecognition
        A.atlas.saturatedAtlas_hasAllLocalDomains).eval V hV).comp
          (g.fullRecognitionPairs.pullback V W hVW).toAlgHom := by
  obtain ⟨S, hqS, hSV⟩ := A.localDomainToFullRecognition.exists_admissible_mem
    A.atlas.saturatedAtlas_hasAllLocalDomains q.point V hV
  have hS : range (A.atlas.saturatedAtlas.chart S) ⊆ V.locus := by
    rw [← V.range_chart]
    intro x hx
    exact hSV ⟨x, hx, rfl⟩
  have hSW : g.toFullRecognitionTarget.baseMap ''
      range (A.atlas.saturatedAtlas.chart S) ⊆ range W.chart := by
    rintro _ ⟨x, hx, rfl⟩
    exact hVW ⟨x, V.range_chart.symm ▸ hS hx, rfl⟩
  calc
    _ = (q.eval S hqS).comp (g.toFullRecognitionTarget.pullback S W hSW).toAlgHom :=
      q.map_eval g.toFullRecognitionTarget
        A.atlas.saturatedAtlas_hasAllLocalDomains W hW S hqS hSW
    _ = (q.eval S hqS).comp
        ((V.originalRestriction S hS).comp
          (g.fullRecognitionPairs.pullback V W hVW)).toAlgHom :=
      congrArg (fun f : BoundedAlgHom K W.algebra (A.atlas.saturatedAtlas.algebra S) =>
        (q.eval S hqS).comp f.toAlgHom)
          (g.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension
            V W hVW S hS).symm
    _ = _ :=
      congrArg (fun e : V.algebra →ₐ[K] L =>
        e.comp (g.fullRecognitionPairs.pullback V W hVW).toAlgHom)
          (q.map_eval A.localDomainToFullRecognition
            A.atlas.saturatedAtlas_hasAllLocalDomains V hV S hqS hSV).symm

end FieldPoint

namespace StrongHom

/-- A full field-valued lift at the specified source point, with exactly
the prescribed image under the actual saturated strong map. -/
def HasFieldPointLiftAt
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) (p : FieldPoint L B.saturatedPresentation) : Prop :=
  ∃ q : FieldPoint L A.saturatedPresentation,
    q.point = y ∧ q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = p

/-- The finite one-chart lift extends to a full field point, conditional
only on the domain completed-residue comparison. -/
theorem IsFiniteAt.hasFieldPointLiftAt
    [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    (hd : PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement.{u})
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    {y : A.space} (hg : g.IsFiniteAt y)
    (p : FieldPoint L B.saturatedPresentation) (hp : p.point = g.baseMap y) :
    g.HasFieldPointLiftAt y p := by
  let p' := p.map B.localDomainToFullRecognition B.atlas.saturatedAtlas_hasAllLocalDomains
  obtain ⟨V, W, hVW, s, hw, c, hs, -, hcn, hcr⟩ :=
    hg.hasFiniteCharacterLiftAt p' hp
  obtain ⟨q', ⟨hq', hV, hc⟩, -⟩ :=
    FieldPoint.existsUnique_of_chartCharacter (A := A.fullRecognitionPresentation)
      hd y V c.toAlgHom ⟨s, hs, hcn⟩
  let q := FieldPoint.comapQuasiIso A.localDomainToFullRecognition_isQuasiIso
    A.fullRecognitionPresentation_hasAllLocalDomains q'
  have hqq : q.map A.localDomainToFullRecognition
      A.atlas.saturatedAtlas_hasAllLocalDomains = q' :=
    FieldPoint.map_comapQuasiIso A.localDomainToFullRecognition_isQuasiIso
      A.fullRecognitionPresentation_hasAllLocalDomains
      A.atlas.saturatedAtlas_hasAllLocalDomains q'
  have hqy : q.point = y := by
    have he := congrArg FieldPoint.point hqq
    change q.point = q'.point at he
    exact he.trans hq'
  refine ⟨q, hqy, ?_⟩
  apply FieldPoint.map_injective B.localDomainToFullRecognition_isQuasiIso
    B.fullRecognitionPresentation_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains
  refine (q.map_saturatedComp g B.localDomainToFullRecognition
    A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains).symm.trans ?_
  change q.map g.toFullRecognitionTarget A.atlas.saturatedAtlas_hasAllLocalDomains = p'
  have hpt : (q.map g.toFullRecognitionTarget
      A.atlas.saturatedAtlas_hasAllLocalDomains).point = p'.point := by
    change g.baseMap q.point = p.point
    rw [hqy, hp]
  have hW : g.baseMap q.point ∈ range W.chart := by
    rw [hqy, ← hp]
    exact hw
  have hVq : q.point ∈ range V.chart := by
    rw [hqy, ← hq']
    exact hV
  apply FieldPoint.eq_of_eval_eq (A := B.fullRecognitionPresentation) hd hpt W hW hw
  rw [q.map_toFullRecognitionTarget_eval g V W hVW hVq hW,
    FieldPoint.eval_congr hqq V hVq hV, hc]
  exact hcr

end StrongHom

end Langlands.Analytic.AffinoidAtlasPresentation

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- The remaining domain residue comparison supplies strong étale image
lifting via local finiteness and the full field-point lift. -/
theorem strongEtaleFieldPointImageLift_of_domain
    (hd : PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement.{u}) :
    StrongEtaleFieldPointImageLiftStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ A B g hg p hp
  obtain ⟨y, hy⟩ := hp
  obtain ⟨q, -, hq⟩ :=
    (hg.isEtale.isQuasifinite y).hasFieldPointLiftAt hd p hy.symm
  exact ⟨q, hq⟩

end Langlands.Analytic.SaturatedAtlasPresentation
