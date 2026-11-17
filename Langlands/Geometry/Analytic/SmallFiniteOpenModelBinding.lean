import Langlands.Geometry.Analytic.FiniteOpenModelChartBinding
import Langlands.Geometry.Analytic.LocalDomainSaturatedTransport
import Langlands.Geometry.Analytic.FibreProductSmallAtlas

/-! # Finite-open model diagrams in the canonical small product -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
  (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
  [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]

/-- The actual canonical small atlas of the recognized cospan. -/
abbrev recognitionSmallProductAtlas : IndexedAffinoidAtlas.{u, v, v} K
    (Shrink.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space) :=
  FibreProduct.smallAtlas f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains

/-- The canonical shrinking homeomorphism of the entire original quotient. -/
abbrev recognitionProductShrink :=
  Shrink.homeomorph (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space

/-- Canonical shrinking of the original good-chart index universe. -/
abbrev recognitionProductIndexEquiv :=
  (equivShrink (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)).symm

namespace FiniteOpenBaseChangeModels

open FiniteAffinoidAlgebraDescent

variable {f g}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)
  (OA : Set A.space) (OB : Set B.space) (hOA : IsOpen OA) (hOB : IsOpen OB)
  [hOAT : T2Space OA] [hOBT : T2Space OB] (hV : V ⊆ OA) (hR : R.locus ⊆ OB)
  [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]

/-- The unchanged actual model domain gives an original small saturated index. -/
def smallModelIndex (i : Fin M.rightCover.cover.size) :
    (recognitionSmallProductAtlas f g).saturatedAtlas.Index :=
  LocalDomain.transportedSaturatedIndex (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.modelDomain OA OB hOA hOB hV hR i)

/-- The entire original overlap domain gives an original small saturated index. -/
def smallOverlapIndex (i j : Fin M.rightCover.cover.size) :
    (recognitionSmallProductAtlas f g).saturatedAtlas.Index :=
  LocalDomain.transportedSaturatedIndex (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.overlapDomain OA OB hOA hOB hV hR i j)

/-- Full comparison from the unchanged finite local algebra to the small chart. -/
def smallModelEquiv (i : Fin M.rightCover.cover.size) :
    BoundedAlgEquiv K (M.algebra i)
      ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
        (M.smallModelIndex OA OB hOA hOB hV hR i)) :=
  LocalDomain.transportedSaturatedEquiv (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.modelDomain OA OB hOA hOB hV hR i)

/-- Full comparison from the unchanged iterated overlap pushout to the small chart. -/
def smallOverlapEquiv (i j : Fin M.rightCover.cover.size) :
    BoundedAlgEquiv K (M.modelOverlapDomain i j).algebra
      ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
        (M.smallOverlapIndex OA OB hOA hOB hV hR i j)) :=
  LocalDomain.transportedSaturatedEquiv (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.overlapDomain OA OB hOA hOB hV hR i j)

theorem range_smallModelIndex (i : Fin M.rightCover.cover.size) :
    range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallModelIndex OA OB hOA hOB hV hR i)) =
        (recognitionProductShrink f g) '' range (M.productChart i) :=
  (LocalDomain.range_transportedSaturatedIndex (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.modelDomain OA OB hOA hOB hV hR i)).trans
      (congrArg (fun S => (recognitionProductShrink f g) '' S)
        (M.modelDomain_locus OA OB hOA hOB hV hR i))

theorem range_smallOverlapIndex (i j : Fin M.rightCover.cover.size) :
    range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallOverlapIndex OA OB hOA hOB hV hR i j)) =
        range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
          (M.smallModelIndex OA OB hOA hOB hV hR i)) ∩
        range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
          (M.smallModelIndex OA OB hOA hOB hV hR j)) := by
  have h := (LocalDomain.range_transportedSaturatedIndex (recognitionProductAtlas f g)
    (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
    (M.overlapDomain OA OB hOA hOB hV hR i j)).trans
      (congrArg (fun S => (recognitionProductShrink f g) '' S)
        (M.overlapDomain_locus OA OB hOA hOB hV hR i j))
  exact h.trans ((image_inter (recognitionProductShrink f g).injective).trans
    (congrArg₂ (fun S T => S ∩ T)
      (M.range_smallModelIndex OA OB hOA hOB hV hR i).symm
      (M.range_smallModelIndex OA OB hOA hOB hV hR j).symm))

theorem smallModelEquiv_chart (i : Fin M.rightCover.cover.size)
    (x : BanachSpectrum ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
      (M.smallModelIndex OA OB hOA hOB hV hR i))) :
    recognitionProductShrink f g
      (M.productChart i ((M.smallModelEquiv OA OB hOA hOB hV hR i).spectrumHomeomorph x)) =
        (recognitionSmallProductAtlas f g).saturatedAtlas.chart
          (M.smallModelIndex OA OB hOA hOB hV hR i) x := by
  exact (congrArg (recognitionProductShrink f g)
    (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR i (Domain.whole K (M.algebra i))
      ((M.smallModelEquiv OA OB hOA hOB hV hR i).spectrumHomeomorph x))).symm.trans
    (LocalDomain.transportedSaturatedEquiv_chart (recognitionProductAtlas f g)
      (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
      (M.modelDomain OA OB hOA hOB hV hR i) x)

theorem smallOverlapEquiv_chart (i j : Fin M.rightCover.cover.size)
    (x : BanachSpectrum ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
      (M.smallOverlapIndex OA OB hOA hOB hV hR i j))) :
    recognitionProductShrink f g
      (M.productChart j ((M.modelOverlapDomain i j).spectrumMap
        ((M.smallOverlapEquiv OA OB hOA hOB hV hR i j).spectrumHomeomorph x))) =
      (recognitionSmallProductAtlas f g).saturatedAtlas.chart
        (M.smallOverlapIndex OA OB hOA hOB hV hR i j) x := by
  exact (congrArg (recognitionProductShrink f g)
    (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)
      ((M.smallOverlapEquiv OA OB hOA hOB hV hR i j).spectrumHomeomorph x))).symm.trans
    (LocalDomain.transportedSaturatedEquiv_chart (recognitionProductAtlas f g)
      (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
      (M.overlapDomain OA OB hOA hOB hV hR i j) x)

/-- Both original whole overlap arrows are transported before saturation;
their complete coefficient maps bind the algebraic descent data in the
canonical small product, with no equality-of-universes hypothesis. -/
def smallChartBinding :
    ChartBinding M.algebraDescentData.toPairTransitions
      (recognitionSmallProductAtlas f g).saturatedAtlas :=
  ChartBinding.ofOverlapComparison M.algebraDescentData.toPairTransitions _
    (M.smallModelIndex OA OB hOA hOB hV hR)
    (M.smallOverlapIndex OA OB hOA hOB hV hR)
    (M.range_smallOverlapIndex OA OB hOA hOB hV hR)
    (M.smallModelEquiv OA OB hOA hOB hV hR)
    (fun i j => (M.modelOverlapDomain i j).algebra)
    M.modelOverlapComparison (M.smallOverlapEquiv OA OB hOA hOB hV hR)
    (fun i j => LocalDomain.transportedSaturatedEquiv_naturality (recognitionProductAtlas f g)
      (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
      (M.overlapToModelLeft OA OB hOA hOB hV hR i j))
    (fun i j => (LocalDomain.transportedSaturatedEquiv_naturality (recognitionProductAtlas f g)
      (recognitionProductShrink f g) (recognitionProductIndexEquiv f g)
      (M.overlapToModelRight OA OB hOA hOB hV hR i j)).trans
        (congrArg (fun z : BoundedAlgHom K (M.algebra j) (M.modelOverlapDomain i j).algebra =>
          (M.smallOverlapEquiv OA OB hOA hOB hV hR i j).toBoundedAlgHom.comp z)
            (M.modelOverlapComparison_comp_localMap i j).symm))

/-- The finite small chart union is the image of the entire literal raw preimage. -/
theorem smallChartBinding_locus :
    (M.smallChartBinding OA OB hOA hOB hV hR).gluingData.locus =
      (recognitionProductShrink f g) ''
        (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
          FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus) := by
  exact (congrArg (fun F : Fin M.rightCover.cover.size →
    Set (Shrink.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space) =>
      ⋃ i, F i) (funext (M.range_smallModelIndex OA OB hOA hOB hV hR))).trans
        ((image_iUnion).symm.trans (congrArg (fun S => (recognitionProductShrink f g) '' S)
          (M.iUnion_range_productChart)))

/-- In the canonical small space the union is the literal simultaneous
preimage under the canonical continuous factor projections. -/
theorem smallChartBinding_locus_eq_preimage :
    (M.smallChartBinding OA OB hOA hOB hV hR).gluingData.locus =
      (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' V ∩
      (FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' R.locus := by
  apply (M.smallChartBinding_locus OA OB hOA hOB hV hR).trans
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap
        ((recognitionProductShrink f g).symm ((recognitionProductShrink f g) x)) ∈ V ∧
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap
        ((recognitionProductShrink f g).symm ((recognitionProductShrink f g) x)) ∈ R.locus
    rw [Homeomorph.symm_apply_apply]
    exact hx
  · intro hz
    exact ⟨(recognitionProductShrink f g).symm z, hz,
      (recognitionProductShrink f g).apply_symm_apply z⟩

end FiniteOpenBaseChangeModels
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
