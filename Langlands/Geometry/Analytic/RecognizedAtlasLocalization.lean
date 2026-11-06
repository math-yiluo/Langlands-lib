import Langlands.Geometry.Analytic.RecognizedAtlasExtension
import Langlands.Geometry.Analytic.CompatibleStrongLocalization

/-! # Recognition in the actual compatible atlas localization -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas.RecognizedSubset

variable {X : Type v} [TopologicalSpace X]
  {a : IndexedAffinoidAtlas.{u, v, w} K X} (V W : a.RecognizedSubset)

/-- The unchanged original algebra gives coherent bounded maps into any two
recognized containing charts, after every presented-affinoid coefficient test. -/
theorem originalRestriction_isMapChartChange (i : a.Index)
    (hV : Set.range (a.chart i) ⊆ V.locus)
    (hW : Set.range (a.chart i) ⊆ W.locus) :
    a.recognitionAtlas.IsMapChartChange V W (a.algebra i)
      (V.originalRestriction i hV) (W.originalRestriction i hW) := by
  let I : a.RecognizedSubset := a.originalRecognitionIndex i
  have hI : I.locus = Set.range (a.chart i) := rfl
  have hIV : I.locus ⊆ V.locus := hI.subset.trans hV
  have hIW : I.locus ⊆ W.locus := hI.subset.trans hW
  have hi : Set.range (a.chart i) ⊆ I.locus := hI.symm.subset
  have hIV' : Set.range (a.recognitionAtlas.chart I) ⊆
      Set.range (a.recognitionAtlas.chart V) := by
    change Set.range I.chart ⊆ Set.range V.chart
    rw [I.range_chart, V.range_chart]
    exact hIV
  have hIW' : Set.range (a.recognitionAtlas.chart I) ⊆
      Set.range (a.recognitionAtlas.chart W) := by
    change Set.range I.chart ⊆ Set.range W.chart
    rw [I.range_chart, W.range_chart]
    exact hIW
  intro T η M hMV hMW α hα
  have hηV : (η.comp (I.originalRestriction i hi)).comp
      (a.recognitionAtlas.restriction I V hIV') = η.comp (V.originalRestriction i hV) :=
    congrArg (fun q : BoundedAlgHom K V.algebra (a.algebra i) => η.comp q)
      (I.originalRestriction_comp_restriction V hIV i hi)
  have hηW : (η.comp (I.originalRestriction i hi)).comp
      (a.recognitionAtlas.restriction I W hIW') = η.comp (W.originalRestriction i hW) :=
    congrArg (fun q : BoundedAlgHom K W.algebra (a.algebra i) => η.comp q)
      (I.originalRestriction_comp_restriction W hIW i hi)
  exact hηW.symm.trans
    (a.recognitionAtlas.originalChartRestriction_test_overlap V W I M
      hIV' hIW' hMV hMW T (η.comp (I.originalRestriction i hi)) α
      (hηV.trans hα.symm))

end IndexedAffinoidAtlas.RecognizedSubset

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Full coefficient coherence of the constructed recognition extension.
Neither source saturation nor an inverse strong map is assumed. -/
theorem toRecognition_hasCoherentPullbacks : A.toRecognition.HasCoherentPullbacks := by
  intro i V W hV hW
  have hiV : Set.range (A.atlas.chart i.down) ⊆ V.down.locus := by
    rw [← V.down.range_chart]
    change id '' Set.range (A.atlas.chart i.down) ⊆ Set.range V.down.chart at hV
    simpa only [Set.image_id] using hV
  have hiW : Set.range (A.atlas.chart i.down) ⊆ W.down.locus := by
    rw [← W.down.range_chart]
    change id '' Set.range (A.atlas.chart i.down) ⊆ Set.range W.down.chart at hW
    simpa only [Set.image_id] using hW
  intro T η M hMV hMW α hα
  exact V.down.originalRestriction_isMapChartChange W.down i.down hiV hiW
    T η M.down hMV hMW α hα

/-- The original presentation with canonically lifted indices, viewed in
its actual compatible strong-map category. -/
def compatibleRecognitionSource : CompatibleAtlasPresentation.{u, v, max v w} K :=
  ⟨A.saturationSource⟩

/-- The constructed recognized presentation in the same compatible category. -/
def compatibleRecognitionTarget : CompatibleAtlasPresentation.{u, v, max v w} K :=
  ⟨A.recognitionTarget⟩

/-- The actual bounded recognition family satisfies the original local
compatibility law and hence is a morphism of the existing category. -/
def compatibleToRecognition : A.compatibleRecognitionSource ⟶ A.compatibleRecognitionTarget where
  toStrongHom := A.toRecognition
  compatible := A.toRecognition.hasLocallyCompatiblePullbacks_iff.mpr
    A.toRecognition_hasCoherentPullbacks

@[simp]
theorem compatibleToRecognition_baseMap :
    A.compatibleToRecognition.baseMap = ContinuousMap.id A.space := rfl

/-- The constructed full-domain recognition extension represents an
isomorphism in the actual category of fractions. -/
def localizedRecognitionIso :
    CompatibleAtlasPresentation.localizationFunctor.obj A.compatibleRecognitionSource ≅
      CompatibleAtlasPresentation.localizationFunctor.obj A.compatibleRecognitionTarget :=
  CompatibleAtlasPresentation.localizedQuasiIso A.compatibleToRecognition
    A.toRecognition_isQuasiIso

@[simp]
theorem localizedRecognitionIso_hom :
    A.localizedRecognitionIso.hom =
      CompatibleAtlasPresentation.localizationFunctor.map A.compatibleToRecognition := rfl

@[simp]
theorem localizedRecognitionIso_hom_space :
    CompatibleAtlasPresentation.localizedSpaceFunctor.map A.localizedRecognitionIso.hom =
      𝟙 A.space := by
  rw [localizedRecognitionIso_hom,
    CompatibleAtlasPresentation.localizedSpaceFunctor_map]
  rfl

/-- The formal inverse induces precisely the identity continuous map on
the unchanged ambient space. It is not supplied as a raw strong map. -/
@[simp]
theorem localizedRecognitionIso_inv_space :
    CompatibleAtlasPresentation.localizedSpaceFunctor.map A.localizedRecognitionIso.inv =
      𝟙 A.space := by
  have h := congrArg
    (CompatibleAtlasPresentation.localizedSpaceFunctor (K := K)).map
    A.localizedRecognitionIso.hom_inv_id
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    A.localizedRecognitionIso_hom_space] at h
  let f : A.space ⟶ A.space :=
    CompatibleAtlasPresentation.localizedSpaceFunctor.map A.localizedRecognitionIso.inv
  have hf : (𝟙 A.space) ≫ f = 𝟙 A.space := h
  exact (Category.id_comp f).symm.trans hf

end AffinoidAtlasPresentation
end Langlands.Analytic
