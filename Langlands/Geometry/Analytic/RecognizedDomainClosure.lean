import Langlands.Geometry.Analytic.RecognizedDomainSpecialCover
import Langlands.Geometry.Analytic.SpecialAffinoidRealizationRecognition

/-! # Constructed recognition and local-domain closure of the full atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace SpecialSubset

variable (W : a.SpecialSubset)

/-- The constructed parent/sections equivalence recovers the actual parent
point under the unchanged canonical map of the literal special subset. -/
theorem realizationSectionEquiv_spectrumMap (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) (x : W.val) :
    (W.realizationSectionEquiv d hd c).spectrumHomeomorph (W.spectrumMap x) =
      c.locusHomeomorph ((Homeomorph.setCongr hd).symm x) := by
  let z := (Homeomorph.setCongr hd).symm x
  have hw :
      (W.comparisonEquiv d hd).spectrumHomeomorph (d.spectrumMap z) =
        W.spectrumMap x :=
    W.comparisonEquiv_spectrumMap d hd z
  have hz :
      (W.comparisonEquiv d hd).spectrumHomeomorph.symm (W.spectrumMap x) =
        d.spectrumMap z :=
    (congrArg (W.comparisonEquiv d hd).spectrumHomeomorph.symm hw).symm.trans
      ((W.comparisonEquiv d hd).spectrumHomeomorph.symm_apply_apply _)
  change c.sectionAlgEquiv.spectrumHomeomorph
    ((W.comparisonEquiv d hd).spectrumHomeomorph.symm (W.spectrumMap x)) = _
  rw [hz, c.spectrumMap_eq_parent z]
  exact c.sectionAlgEquiv.spectrumHomeomorph.apply_symm_apply _

/-- Any presentation produced by the intrinsic recognition criterion has
exactly the parent chart after the actual bounded algebra comparison. -/
theorem chart_affinoidRealization
    (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap)
    (d : FiniteChartGluingData a) (hd : d.locus = W.val)
    (c : d.AffinoidRealization) (x : BanachSpectrum h.presentation) :
    W.chart h hb x =
      c.chart (((W.realizationSectionEquiv d hd c).trans
        h.presentationEquiv.symm).spectrumHomeomorph x) := by
  let e := (W.realizationSectionEquiv d hd c).trans h.presentationEquiv.symm
  let y := (W.coordinates h hb).symm x
  let z := (Homeomorph.setCongr hd).symm y
  have hy : W.coordinates h hb y = x := (W.coordinates h hb).apply_symm_apply x
  have he :
      e.spectrumHomeomorph (W.coordinates h hb y) = c.locusHomeomorph z := by
    change (W.realizationSectionEquiv d hd c).spectrumHomeomorph
      (h.presentationEquiv.spectrumHomeomorph.symm
        (h.presentationEquiv.spectrumHomeomorph (W.spectrumMap y))) = _
    rw [h.presentationEquiv.spectrumHomeomorph.symm_apply_apply]
    exact W.realizationSectionEquiv_spectrumMap d hd c y
  have hx : e.spectrumHomeomorph x = c.locusHomeomorph z :=
    (congrArg e.spectrumHomeomorph hy).symm.trans he
  have hc : c.chart (c.locusHomeomorph z) = (z : X) :=
    congrArg Subtype.val (c.locusHomeomorph.symm_apply_apply z)
  exact ((congrArg c.chart hx).trans hc).symm

end SpecialSubset

variable (a) (V : a.saturatedAtlas.RecognizedSubset) (D : Domain K V.algebra)

/-- All three intrinsic recognition conditions for the actual domain
follow from its constructed finite realization and tensor-special cover. -/
theorem fullRecognitionDomainSpecialSubset_isRecognized :
    (a.fullRecognitionDomainSpecialSubset V D).IsRecognized :=
  (a.fullRecognitionDomainSpecialSubset V D).isRecognized_of_affinoidRealization
    (a.fullRecognitionDomainGluing V D) (a.fullRecognitionDomainGluing_locus V D)
    (a.fullRecognitionDomainGluing_isSpecialCover V D)
    (a.fullRecognitionDomainAffinoidRealization V D)

/-- The unchanged domain locus is an actual recognized chart of the same
full recognition atlas, without supplying any recognition output. -/
def fullRecognitionDomainRecognizedSubset : a.saturatedAtlas.RecognizedSubset :=
  ⟨a.fullRecognitionDomainSpecialSubset V D,
    a.fullRecognitionDomainSpecialSubset_isRecognized V D⟩

@[simp]
theorem fullRecognitionDomainRecognizedSubset_locus :
    (a.fullRecognitionDomainRecognizedSubset V D).locus = V.domainLocus D := rfl

/-- The actual domain algebra is bounded equivalent to the finite Tate
presentation constructed from its unchanged canonical section algebra. -/
def fullRecognitionDomainAlgebraEquiv :
    BoundedAlgEquiv K D.algebra (a.fullRecognitionDomainRecognizedSubset V D).algebra :=
  ((a.fullRecognitionDomainSpecialSubset V D).realizationSectionEquiv
    (a.fullRecognitionDomainGluing V D) (a.fullRecognitionDomainGluing_locus V D)
    (a.fullRecognitionDomainAffinoidRealization V D)).trans
      (a.fullRecognitionDomainRecognizedSubset V D).property.algebraEquiv.symm

/-- The newly recognized chart recovers exactly the original domain chart,
through the spectrum homeomorphism of the constructed bounded equivalence. -/
theorem fullRecognitionDomainRecognizedSubset_chart
    (x : BanachSpectrum (a.fullRecognitionDomainRecognizedSubset V D).algebra) :
    (a.fullRecognitionDomainRecognizedSubset V D).chart x =
      V.domainAmbientMap D ((a.fullRecognitionDomainAlgebraEquiv V D).spectrumHomeomorph x) :=
  (a.fullRecognitionDomainSpecialSubset V D).chart_affinoidRealization
    (a.fullRecognitionDomainRecognizedSubset V D).property.affinoid
    (a.fullRecognitionDomainRecognizedSubset V D).property.bijective
    (a.fullRecognitionDomainGluing V D) (a.fullRecognitionDomainGluing_locus V D)
    (a.fullRecognitionDomainAffinoidRealization V D) x

/-- Every actual full local domain of the full recognition atlas is already
one of that atlas's original charts, on the same literal ambient subset. -/
theorem fullRecognitionAtlas_localDomain_chart_range (U : LocalDomain a.fullRecognitionAtlas) :
    Set.range (a.fullRecognitionAtlas.chart
      (a.fullRecognitionDomainRecognizedSubset U.index U.domain)) = U.locus :=
  (a.fullRecognitionDomainRecognizedSubset U.index U.domain).range_chart

/-- Closure under every actual local full domain is equality of literal
chart families, rather than merely mutual local refinement. -/
theorem fullRecognitionAtlas_localDomainFamily :
    a.fullRecognitionAtlas.localDomainFamily =
      Set.range (fun i => Set.range (a.fullRecognitionAtlas.chart i)) := by
  apply Set.Subset.antisymm
  · rintro S ⟨U, rfl⟩
    exact ⟨a.fullRecognitionDomainRecognizedSubset U.index U.domain,
      a.fullRecognitionAtlas_localDomain_chart_range U⟩
  · exact a.fullRecognitionAtlas.chartFamily_subset_localDomainFamily

end Langlands.Analytic.IndexedAffinoidAtlas
