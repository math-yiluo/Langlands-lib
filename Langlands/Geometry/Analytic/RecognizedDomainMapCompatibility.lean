import Langlands.Geometry.Analytic.AdmissibleRecognitionSubatlas
import Langlands.Geometry.Analytic.RecognizedLocalDomainCategory

/-! # Complete bounded maps on domains of a recognized source affinoid -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
  (V : A.atlas.saturatedAtlas.RecognizedSubset)

/-- The constructed recognized chart of an actual full domain in V. -/
abbrev domainRecognition (_g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (D : Domain K V.algebra) :
    A.atlas.saturatedAtlas.RecognizedSubset :=
  A.atlas.fullRecognitionLocalDomainFunctor.obj ⟨V, D⟩

/-- The complete original domain algebra is compared with its constructed
recognized algebra by the actual local-domain category equivalence. -/
abbrev domainRecognitionEquiv (D : Domain K V.algebra) :
    BoundedAlgEquiv K D.algebra (g.domainRecognition V D).algebra :=
  A.atlas.fullRecognitionLocalDomainAlgebraEquiv ⟨V, D⟩

theorem domainRecognition_admissible (D : Domain K V.algebra)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus) :
    g.baseMap '' range (g.domainRecognition V D).chart ⊆ range W.chart :=
  ((image_mono (g.domainRecognition V D).range_chart.subset).trans h).trans W.range_chart.symm.subset

/-- The actual full-recognition pullback transported to the unchanged
full-domain algebra. No algebra map is inferred from a spectrum map. -/
def domainRecognitionPullback (D : Domain K V.algebra)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus) :
    BoundedAlgHom K W.algebra D.algebra :=
  (g.domainRecognitionEquiv V D).symm.toBoundedAlgHom.comp
    (g.fullRecognitionPairs.pullback (g.domainRecognition V D) W
      (g.domainRecognition_admissible V D W h))

/-- The transported complete map has exactly the original ambient action. -/
theorem domainRecognitionPullback_chart (D : Domain K V.algebra)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus)
    (x : BanachSpectrum D.algebra) :
    W.chart (BanachSpectrum.comap (g.domainRecognitionPullback V D W h).toBoundedRingHom x) =
      g.baseMap (V.chart (D.spectrumMap x)) := by
  let L : LocalDomain A.atlas.fullRecognitionAtlas := ⟨V, D⟩
  let e := g.domainRecognitionEquiv V D
  exact (g.fullRecognitionPairs.chart_comm (g.domainRecognition V D) W
    (g.domainRecognition_admissible V D W h) (e.spectrumHomeomorph.symm x)).trans
      (congrArg g.baseMap
        ((A.atlas.fullRecognitionLocalDomainAlgebraEquiv_chart L _).trans
          (congrArg L.ambientMap (e.spectrumHomeomorph.apply_symm_apply x))))

/-- Source restriction compatibility follows from the full bounded algebra
naturality of actual domain recognition and the original pair system. -/
theorem domainRecognitionPullback_restriction {D E : Domain K V.algebra}
    (r : E ⟶ D) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hD : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus)
    (hE : g.baseMap '' (V.chart '' E.locus) ⊆ W.locus) :
    r.restriction.comp (g.domainRecognitionPullback V D W hD) =
      g.domainRecognitionPullback V E W hE := by
  let p := (LocalDomain.sameChartFunctor A.atlas.fullRecognitionAtlas V).map r
  let eD := g.domainRecognitionEquiv V D
  let eE := g.domainRecognitionEquiv V E
  have hn := A.atlas.fullRecognitionLocalDomainAlgebraEquiv_naturality p
  have hsub : range (g.domainRecognition V E).chart ⊆ range (g.domainRecognition V D).chart :=
    ((g.domainRecognition V E).range_chart.subset.trans
      (image_mono r.subset)).trans (g.domainRecognition V D).range_chart.symm.subset
  have hp := g.fullRecognitionPairs.restriction_comm
    (g.domainRecognition V E) (g.domainRecognition V D) W W hsub (Subset.refl _)
      (g.domainRecognition_admissible V E W hE) (g.domainRecognition_admissible V D W hD)
  rw [B.fullRecognitionPresentation.atlas.restriction_id W (Subset.refl _),
    BoundedAlgHom.comp_id] at hp
  let qD := g.fullRecognitionPairs.pullback (g.domainRecognition V D) W
    (g.domainRecognition_admissible V D W hD)
  let qE := g.fullRecognitionPairs.pullback (g.domainRecognition V E) W
    (g.domainRecognition_admissible V E W hE)
  apply BoundedAlgHom.ext
  intro x
  apply eE.toAlgEquiv.injective
  change eE (r.restriction (eD.symm (qD x))) = eE (eE.symm (qE x))
  have hn' := congrArg (fun q : BoundedAlgHom K D.algebra (g.domainRecognition V E).algebra =>
    q (eD.symm (qD x))) hn
  exact hn'.trans
    ((congrArg (A.atlas.fullRecognitionLocalDomainFunctor.map p).restriction
      (eD.apply_symm_apply (qD x))).trans
        ((congrArg (fun q : BoundedAlgHom K W.algebra (g.domainRecognition V E).algebra => q x) hp).trans
          (eE.apply_symm_apply (qE x)).symm))

/-- Two target charts give the original full coefficient-test chart change
on an unchanged source domain algebra. -/
theorem domainRecognitionPullback_isMapChartChange (D : Domain K V.algebra)
    (W W' : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus)
    (h' : g.baseMap '' (V.chart '' D.locus) ⊆ W'.locus) :
    B.fullRecognitionPresentation.atlas.IsMapChartChange W W' D.algebra
      (g.domainRecognitionPullback V D W h) (g.domainRecognitionPullback V D W' h') := by
  let I := g.recognitionSourceIndex (g.domainRecognition V D) W
    (g.domainRecognition_admissible V D W h)
  exact (g.compatibleRecognitionMap.coherent I W W'
    (g.domainRecognition_admissible V D W h) (g.domainRecognition_admissible V D W' h')).comp
      B.fullRecognitionPresentation.atlas (g.domainRecognitionEquiv V D).symm.toBoundedAlgHom

/-- On every actual overlap full domain, both local maps are related by
the complete target chart-change law, including all coefficient tests. -/
theorem domainRecognitionPullback_overlap {D E F : Domain K V.algebra}
    (r : F ⟶ D) (s : F ⟶ E) (W W' : B.atlas.saturatedAtlas.RecognizedSubset)
    (hD : g.baseMap '' (V.chart '' D.locus) ⊆ W.locus)
    (hE : g.baseMap '' (V.chart '' E.locus) ⊆ W'.locus) :
    B.fullRecognitionPresentation.atlas.IsMapChartChange W W' F.algebra
      (r.restriction.comp (g.domainRecognitionPullback V D W hD))
      (s.restriction.comp (g.domainRecognitionPullback V E W' hE)) := by
  have hF : g.baseMap '' (V.chart '' F.locus) ⊆ W.locus :=
    (image_mono (image_mono r.subset)).trans hD
  have hF' : g.baseMap '' (V.chart '' F.locus) ⊆ W'.locus :=
    (image_mono (image_mono s.subset)).trans hE
  exact (congrArg₂
    (fun (a : BoundedAlgHom K W.algebra F.algebra)
      (b : BoundedAlgHom K W'.algebra F.algebra) =>
        B.fullRecognitionPresentation.atlas.IsMapChartChange W W' F.algebra a b)
    (g.domainRecognitionPullback_restriction V r W hD hF)
    (g.domainRecognitionPullback_restriction V s W' hE hF')).mpr
      (g.domainRecognitionPullback_isMapChartChange V F W W' hF hF')

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
