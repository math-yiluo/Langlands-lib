import Langlands.Geometry.Analytic.FiniteChartAffinoidRealization
import Langlands.Geometry.Analytic.SpecialAffinoidRecognition

/-! # Recognition constructed from an actual finite affinoid realization -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.SpecialSubset

open Set PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (W : a.SpecialSubset)

/-- The canonical component map has precisely its original ambient
component as its relative spectrum image. No representation is assumed. -/
theorem range_comap_componentRestriction
    (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap)
    (d : FiniteChartGluingData a) (hd : d.locus = W.val) (i : Fin d.size) :
    Set.range (BanachSpectrum.comap (W.componentRestriction h d hd i).toBoundedRingHom) =
      W.chart h hb ⁻¹' Set.range (a.chart (d.index i)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (W.chart_component h hb d hd i y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (W.isEmbedding_chart h hb).injective ?_⟩
    exact (W.chart_component h hb d hd i y).trans hy

/-- Finite full-domain recovery and the actual comparison of defining
covers construct a bounded equivalence with the special-subset sections. -/
def realizationSectionEquiv (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) :
    BoundedAlgEquiv K c.algebra W.SectionAlgebra :=
  c.sectionAlgEquiv.trans (W.comparisonEquiv d hd).symm

/-- The unchanged special-subset section algebra has an actual admissible
finite positive-radius Tate presentation. -/
theorem isAffinoid_of_affinoidRealization (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) :
    IsAffinoidAlgebra K W.SectionAlgebra :=
  c.isAffinoid_sectionAlgebra.of_boundedEquiv (W.comparisonEquiv d hd).symm

/-- The comparison identifies the already constructed canonical point map
with the finite realization's canonical map on the same literal subset. -/
theorem spectrumMap_eq_affinoidRealization (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) :
    W.spectrumMap =
      (W.comparisonEquiv d hd).spectrumHomeomorph ∘ d.spectrumMap ∘
        (Homeomorph.setCongr hd).symm := by
  funext x
  exact (W.comparisonEquiv_spectrumMap d hd ((Homeomorph.setCongr hd).symm x)).symm

theorem spectrumMap_bijective_of_affinoidRealization (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) :
    Function.Bijective W.spectrumMap := by
  rw [W.spectrumMap_eq_affinoidRealization d hd]
  exact (W.comparisonEquiv d hd).spectrumHomeomorph.bijective.comp
    (c.bijective_spectrumMap.comp (Homeomorph.setCongr hd).symm.bijective)

/-- Compare the supplied actual parent with the presentation constructed
from the intrinsic affinoidness of the unchanged section algebra. -/
def realizationPresentationEquiv (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) :
    BoundedAlgEquiv K c.algebra (W.isAffinoid_of_affinoidRealization d hd c).presentation :=
  (W.realizationSectionEquiv d hd c).trans
    (W.isAffinoid_of_affinoidRealization d hd c).presentationEquiv.symm

/-- The canonical component restriction is the original entire bounded
restriction transported by the constructed parent/presentation equivalence. -/
theorem componentRestriction_affinoidRealization (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (c : d.AffinoidRealization) (i : Fin d.size) :
    W.componentRestriction (W.isAffinoid_of_affinoidRealization d hd c) d hd i =
      (c.restriction i).comp (W.realizationPresentationEquiv d hd c).symm.toBoundedAlgHom := by
  apply BoundedAlgHom.ext
  intro b
  exact (congrArg
    (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
      f ((W.comparisonEquiv d hd)
        ((W.isAffinoid_of_affinoidRealization d hd c).presentationEquiv b)))
    (c.restriction_comp_glueToParent i)).symm

/-- Full represented-domain universal properties transport to the
constructed chart, with its exact original ambient component loci. -/
theorem componentRestriction_represents_of_affinoidRealization
    (d : FiniteChartGluingData a) (hd : d.locus = W.val)
    (c : d.AffinoidRealization) (i : Fin d.size) :
    Represents K
      (W.componentRestriction (W.isAffinoid_of_affinoidRealization d hd c) d hd i)
      (W.chart (W.isAffinoid_of_affinoidRealization d hd c)
        (W.spectrumMap_bijective_of_affinoidRealization d hd c) ⁻¹'
          Set.range (a.chart (d.index i))) := by
  let h := W.isAffinoid_of_affinoidRealization d hd c
  let hb := W.spectrumMap_bijective_of_affinoidRealization d hd c
  let e := W.realizationPresentationEquiv d hd c
  have hr := (c.represents i).precomp_equiv e
  have hm := W.componentRestriction_affinoidRealization d hd c i
  have hl : e.spectrumHomeomorph ⁻¹' (c.chart ⁻¹' Set.range (a.chart (d.index i))) =
      W.chart h hb ⁻¹' Set.range (a.chart (d.index i)) := by
    rw [← hr.2.1, ← hm]
    exact W.range_comap_componentRestriction h hb d hd i
  rw [W.componentRestriction_affinoidRealization d hd c i]
  exact hl ▸ hr

/-- All three recognition conditions follow from actual finite affinoid
realization data and specialness of the supplied defining cover. -/
theorem isRecognized_of_affinoidRealization (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (hspecial : d.IsSpecialCover)
    (c : d.AffinoidRealization) : W.IsRecognized :=
  ⟨W.isAffinoid_of_affinoidRealization d hd c,
    W.spectrumMap_bijective_of_affinoidRealization d hd c,
    d, hd, hspecial, W.componentRestriction_represents_of_affinoidRealization d hd c⟩

end Langlands.Analytic.IndexedAffinoidAtlas.SpecialSubset
