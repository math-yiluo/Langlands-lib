import Langlands.Geometry.Analytic.EtaleOpenDomains.Statement
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.FullRecognitionEquivalence
import Langlands.Geometry.Analytic.EtaleOpenDomains.Transport

/-! # Étaleness of open analytic domain inclusions -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace EtaleOpenDomains

omit [CompleteSpace K] in
private theorem finiteBanach_equiv {R S : PresentedAffinoidAlgebra K}
    (e : BoundedAlgEquiv K R S) : e.toBoundedAlgHom.IsFiniteBanach := by
  obtain ⟨C, hC, hb⟩ := e.inverse_bounded
  refine ⟨1, fun _ => 1, C, hC, fun y => ⟨fun _ => e.symm y, ?_, ?_⟩⟩
  · simp [BoundedAlgHom.coefficientMap_apply]
  · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg y))).2
      (fun _ => hb y)

private def RepresentsCharts {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (f : AffinoidAtlasPresentation.StrongHom A B) : Prop :=
  ∀ i j (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
    Represents K (f.pullback i j h) (f.chartImageLocus i j)

private theorem representsCharts_comp {A B C : AffinoidAtlasPresentation.{u, v, v} K}
    (f : AffinoidAtlasPresentation.StrongHom A B)
    (g : AffinoidAtlasPresentation.StrongHom B C)
    (hf : RepresentsCharts f) (hg : RepresentsCharts g)
    (hinj : Function.Injective g.baseMap)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    RepresentsCharts (f.saturatedComp g ha hb) := by
  intro i k h
  obtain ⟨j, hfij⟩ := f.target_exists i
  obtain ⟨p, hgjp⟩ := g.target_exists j
  have hgi : Function.Injective
      (BanachSpectrum.comap (g.pullback j p hgjp).toBoundedRingHom) := by
    intro x y hxy
    apply (B.atlas.isEmbedding_chart j).injective
    apply hinj
    exact (g.chart_comm j p hgjp x).symm.trans
      ((congrArg (C.atlas.chart p) hxy).trans (g.chart_comm j p hgjp y))
  have hchain := (hg j p hgjp).comp_of_injective (hf i j hfij) hgi
  have hchange := C.atlas.represents_changeMapChart p k (A.atlas.algebra i)
    (f.chainPullback g i j p hfij hgjp) hchain
    (f.chainPullback_image_chart g i j p k hfij hgjp h)
  rw [f.mapChartImage_chainPullback g i j p hfij hgjp] at hchange
  change Represents K (f.saturatedCompPullback g i k h)
    (C.atlas.chart k ⁻¹' ((g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i)))
  rw [f.saturatedCompPullback_eq_chainChange g ha hb i j p k hfij hgjp h]
  exact hchange

private theorem representsCharts_domainInclusion
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain) :
    RepresentsCharts (S.domainInclusion D) := by
  intro c j h
  change Represents K (S.presentation.atlas.restriction c.val j _)
    (S.presentation.atlas.chart j ⁻¹' (Subtype.val ''
      Set.range (S.presentation.atlas.subspaceChart D.carrier c)))
  have hr : Subtype.val '' Set.range (S.presentation.atlas.subspaceChart D.carrier c) =
      Set.range (S.presentation.atlas.chart c.val) := by
    rw [← Set.range_comp]
    rfl
  rw [hr]
  exact S.presentation.atlas.restriction_represents c.val j _

private def saturatedInclusion (S : SaturatedAtlasPresentation.{u, v, v} K)
    (D : S.AnalyticDomain) :
    SaturatedAtlasPresentation.ofSaturation (S.domain D).presentation ⟶
      SaturatedAtlasPresentation.ofSaturation S.presentation :=
  ((S.domain D).saturationIso.hom ≫ S.domainInclusion D) ≫ S.saturationIso.inv

private theorem saturatedInclusion_represents
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain) :
    RepresentsCharts (saturatedInclusion S D) := by
  have h₁ := representsCharts_comp (S.domain D).saturationIso.hom (S.domainInclusion D)
    (S.domain D).presentation.isQuasiIso_directFromSaturation.2
    (representsCharts_domainInclusion S D) Subtype.val_injective
    (S.domain D).presentation.atlas.saturatedAtlas_hasAllLocalDomains
    (S.domain D).hasAllLocalDomains
  exact representsCharts_comp _ S.saturationIso.inv h₁
    S.presentation.isQuasiIso_directToSaturation.2 Function.injective_id
    (S.domain D).presentation.atlas.saturatedAtlas_hasAllLocalDomains S.hasAllLocalDomains

private theorem pair_equiv {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (g : AffinoidAtlasPresentation.StrongHom A.saturatedPresentation B.saturatedPresentation)
    (hg : RepresentsCharts g) (S : A.atlas.saturatedAtlas.Index)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (T : B.atlas.saturatedAtlas.Index)
    (himage : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) = W.locus)
    (hT : Set.range (B.atlas.saturatedAtlas.chart T) = W.locus)
    (h : g.baseMap '' Set.range (A.atlas.saturatedAtlas.originalRecognitionIndex S).chart ⊆
      Set.range W.chart) :
    ∃ e : BoundedAlgEquiv K W.algebra
        (A.atlas.saturatedAtlas.originalRecognitionIndex S).algebra,
      e.toBoundedAlgHom = g.fullRecognitionPairs.pullback
        (A.atlas.saturatedAtlas.originalRecognitionIndex S) W h := by
  let V := A.atlas.saturatedAtlas.originalRecognitionIndex S
  have hS := A.atlas.saturatedAtlas.originalRecognitionIndex_range_subset S
  have hST := himage.trans hT.symm
  have hWrep := W.originalRestriction_represents T hT.subset
  rw [W.range_comap_originalRestriction] at hWrep
  have hWuniv : W.chart ⁻¹' Set.range (B.atlas.saturatedAtlas.chart T) = Set.univ := by
    rw [hT, ← W.range_chart]
    exact Set.eq_univ_of_forall fun x => Set.mem_range_self x
  rw [hWuniv] at hWrep
  have hgrep := hg S T hST.subset
  have hguniv : g.chartImageLocus S T = Set.univ := by
    exact Set.eq_univ_of_forall fun x =>
      himage.superset (hT.subset (Set.mem_range_self x))
  rw [hguniv] at hgrep
  let σ := A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv S
  let τ := hWrep.univEquiv
  let μ := hgrep.univEquiv
  refine ⟨(τ.trans μ).trans σ.symm, ?_⟩
  apply BoundedAlgHom.ext
  intro x
  apply σ.injective
  change σ (σ.symm (μ (τ x))) = σ (g.fullRecognitionPairs.pullback V W h x)
  exact (σ.apply_symm_apply _).trans
    (congrArg (fun q : BoundedAlgHom K W.algebra
      (A.atlas.saturatedAtlas.algebra S) => q x)
        (g.originalRestriction_comp_fullRecognitionPairs V W h S hS T hT.subset
          hST.subset)).symm

private theorem finiteEtale_fullRecognitionDomain
    (P : AffinoidAtlasPresentation.{u, v, v} K)
    (D : (SaturatedAtlasPresentation.ofFullRecognition P).AnalyticDomain) :
    (saturatedInclusion (SaturatedAtlasPresentation.ofFullRecognition P) D).IsFiniteEtaleOver
      Set.univ D.carrier := by
  let B := SaturatedAtlasPresentation.ofFullRecognition P
  let A := (B.domain D).presentation
  let g := saturatedInclusion B D
  refine ⟨?_, fun W hW => ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · let i : B.presentation.atlas.Index := P.atlas.fullRecognitionIdempotenceIndex W
    have hi : Set.range (B.presentation.atlas.chart i) = W.locus :=
      (P.atlas.fullRecognitionIdempotenceIndex W).range_chart
    let c : A.atlas.Index := ⟨i, hi.subset.trans hW⟩
    let S := A.atlas.originalSaturatedIndex c
    let T := B.presentation.atlas.originalSaturatedIndex i
    let V : A.atlas.saturatedAtlas.RecognizedSubset :=
      A.atlas.saturatedAtlas.originalRecognitionIndex S
    have hrS : Set.range (A.atlas.saturatedAtlas.chart S) =
        (Subtype.val ⁻¹' W.locus : Set D.carrier) :=
      (A.atlas.saturatedAtlas_original_range c).trans
        ((B.presentation.atlas.range_subspaceChart D.carrier c).trans
          (congrArg (fun E => (Subtype.val ⁻¹' E : Set D.carrier)) hi))
    have hrT : Set.range (B.presentation.atlas.saturatedAtlas.chart T) = W.locus :=
      (B.presentation.atlas.saturatedAtlas_original_range i).trans hi
    have himage : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) = W.locus := by
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hrS.subset hx
      · intro x hx
        exact ⟨⟨x, hW hx⟩, hrS.superset hx, rfl⟩
    have hV : V.locus = Set.range (A.atlas.saturatedAtlas.chart S) :=
      V.range_chart.symm.trans (A.atlas.saturatedAtlas.recognitionAtlas_original_range S)
    have hadm : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart :=
      (Set.image_mono (V.range_chart.trans hV).subset).trans
        (himage.trans W.range_chart.symm).subset
    have hloc : V.locus = Set.univ ∩ g.baseMap ⁻¹' W.locus := by
      exact hV.trans (hrS.trans (Set.univ_inter _).symm)
    obtain ⟨e, he⟩ := pair_equiv g (saturatedInclusion_represents B D)
      S W T himage hrT hadm
    refine ⟨V, hadm, hloc, ?_⟩
    rw [← he]
    exact ⟨finiteBanach_equiv e,
      BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ e.toAlgEquiv.bijective⟩

end EtaleOpenDomains

namespace SaturatedAtlasPresentation

open EtaleOpenDomains

/-- Open-domain inclusions are étale on the full-recognition presentation. -/
theorem etale_openDomain_fullRecognition (P : AffinoidAtlasPresentation.{u, v, v} K)
    (U : Set P.space) (hU : IsOpen U) :
    etale ((ofFullRecognition P).localizedDomainInclusion
      ((ofFullRecognition P).openDomain U hU)) := by
  let B := ofFullRecognition P
  let D := B.openDomain U hU
  let g := saturatedInclusion B D
  have hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces
      (A := (B.domain D).presentation) (B := B.presentation) g := by
    intro y
    apply AffinoidAtlasPresentation.StrongHom.IsLocallyFiniteEtaleAt.isEtaleAtAllPieces
    exact ⟨Set.univ, U, isOpen_univ, hU, Set.mem_univ y,
      finiteEtale_fullRecognitionDomain P D⟩
  refine ⟨(B.domain D).presentation, B.presentation, g, hg,
    ⟨Arrow.isoMk (localizationFunctor.mapIso (B.domain D).saturationIso)
      (localizationFunctor.mapIso B.saturationIso) ?_⟩⟩
  change localizationFunctor.map (B.domain D).saturationIso.hom ≫
      localizationFunctor.map (B.domainInclusion D) =
    localizationFunctor.map g ≫ localizationFunctor.map B.saturationIso.hom
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [g, EtaleOpenDomains.saturatedInclusion, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Every canonical inclusion of an open analytic domain is étale. -/
theorem etaleOpenDomainStatement (X : LocalizedCategory.{u, v, v} (K := K)) :
    EtaleOpenDomainStatement X :=
  etaleOpenDomainStatement_of_fullRecognition etale_openDomain_fullRecognition X

end SaturatedAtlasPresentation
end Langlands.Analytic
