import Langlands.Geometry.Analytic.SpecialSubsetSections
import Langlands.Geometry.Analytic.IntrinsicAffinoidAlgebra
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport

/-! # Constructed affinoid charts recognized from special-subset sections -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.SpecialSubset

open Set PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (W : a.SpecialSubset)

instance : CompactSpace W.val :=
  (Homeomorph.setCongr W.gluingData_locus).compactSpace

instance : T2Space W.val :=
  (Homeomorph.setCongr W.gluingData_locus).t2Space

/-- Compactness upgrades bijectivity of the already constructed continuous
canonical map to an actual homeomorphism. -/
def spectrumHomeomorph (hb : Function.Bijective W.spectrumMap) :
    W.val ≃ₜ BanachSpectrum W.SectionAlgebra :=
  W.spectrumMap.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective W.spectrumMap hb)

@[simp]
theorem spectrumHomeomorph_apply (hb : Function.Bijective W.spectrumMap) (x : W.val) :
    W.spectrumHomeomorph hb x = W.spectrumMap x := rfl

/-- Intrinsic affinoidness constructs the finite presentation, and the two
actual spectrum maps give coordinates on the unchanged literal subset. -/
def coordinates (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap) :
    W.val ≃ₜ BanachSpectrum h.presentation :=
  (W.spectrumHomeomorph hb).trans h.presentationEquiv.spectrumHomeomorph

/-- The new chart is the inverse of the canonical coordinate map followed
by the literal inclusion into the original ambient space. -/
def chart (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap) :
    C(BanachSpectrum h.presentation, X) where
  toFun x := (W.coordinates h hb).symm x
  continuous_toFun := continuous_subtype_val.comp (W.coordinates h hb).symm.continuous

theorem isEmbedding_chart (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap) : IsEmbedding (W.chart h hb) :=
  IsEmbedding.subtypeVal.comp (W.coordinates h hb).symm.isEmbedding

theorem range_chart (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap) : Set.range (W.chart h hb) = W.val := by
  change Set.range (Subtype.val ∘ (W.coordinates h hb).symm) = W.val
  rw [Set.range_comp, (W.coordinates h hb).symm.surjective.range_eq]
  simpa only [Set.image_univ] using (Subtype.range_coe (s := W.val))

/-- The original chart components map to the constructed finite
presentation by the actual equalizer comparison and projections. -/
def componentRestriction (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (d : FiniteChartGluingData a) (hd : d.locus = W.val) (i : Fin d.size) :
    BoundedAlgHom K h.presentation (a.algebra (d.index i)) :=
  ((d.projection i).comp (W.comparisonEquiv d hd).toBoundedAlgHom).comp
    h.presentationEquiv.toBoundedAlgHom

/-- The actual bounded component map recovers its unchanged original
ambient chart under the constructed coordinates. -/
theorem component_coordinates (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap)
    (d : FiniteChartGluingData a) (hd : d.locus = W.val) (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    BanachSpectrum.comap (W.componentRestriction h d hd i).toBoundedRingHom x =
      W.coordinates h hb ⟨a.chart (d.index i) x,
        hd ▸ Set.mem_iUnion.mpr ⟨i, x, rfl⟩⟩ := by
  have hc := W.comparisonEquiv_spectrumMap d hd (d.componentMap i x)
  rw [d.spectrumMap_componentMap] at hc
  exact congrArg h.presentationEquiv.spectrumHomeomorph hc

theorem chart_component (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (hb : Function.Bijective W.spectrumMap)
    (d : FiniteChartGluingData a) (hd : d.locus = W.val) (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    W.chart h hb
        (BanachSpectrum.comap (W.componentRestriction h d hd i).toBoundedRingHom x) =
      a.chart (d.index i) x := by
  rw [W.component_coordinates h hb d hd i x]
  exact congrArg Subtype.val ((W.coordinates h hb).symm_apply_apply _)

/-- The source recognition criterion restricted to finite special covers
by the original indexed charts. All three conditions are retained. -/
def IsRecognized : Prop :=
  ∃ h : IsAffinoidAlgebra K W.SectionAlgebra,
    ∃ hb : Function.Bijective W.spectrumMap,
      ∃ d : FiniteChartGluingData a, ∃ hd : d.locus = W.val,
        d.IsSpecialCover ∧
          ∀ i, Represents K (W.componentRestriction h d hd i)
            (W.chart h hb ⁻¹' Set.range (a.chart (d.index i)))

namespace IsRecognized

variable {W} (hW : W.IsRecognized)

include hW in
theorem affinoid : IsAffinoidAlgebra K W.SectionAlgebra := hW.choose

include hW in
theorem bijective : Function.Bijective W.spectrumMap := hW.choose_spec.choose

/-- This actual finite weighted Tate quotient is constructed from the
intrinsic section-algebra criterion. -/
def algebra : PresentedAffinoidAlgebra K := hW.affinoid.presentation

def algebraEquiv : BoundedAlgEquiv K hW.algebra W.SectionAlgebra :=
  hW.affinoid.presentationEquiv

def chart : C(BanachSpectrum hW.algebra, X) := W.chart hW.affinoid hW.bijective

theorem isEmbedding_chart : IsEmbedding hW.chart :=
  W.isEmbedding_chart hW.affinoid hW.bijective

theorem range_chart : Set.range hW.chart = W.val :=
  W.range_chart hW.affinoid hW.bijective

def cover : FiniteChartGluingData a := hW.choose_spec.choose_spec.choose

theorem cover_locus : hW.cover.locus = W.val :=
  hW.choose_spec.choose_spec.choose_spec.choose

theorem cover_isSpecial : hW.cover.IsSpecialCover :=
  hW.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- Every selected component is a full affinoid domain in the constructed
chart, with its unchanged original algebra and actual projection map. -/
def componentDomain (i : Fin hW.cover.size) : Domain K hW.algebra where
  algebra := a.algebra (hW.cover.index i)
  baseMap := W.componentRestriction hW.affinoid hW.cover hW.cover_locus i
  locus := hW.chart ⁻¹' Set.range (a.chart (hW.cover.index i))
  represents := hW.choose_spec.choose_spec.choose_spec.choose_spec.2 i

theorem componentDomain_over_ambient (i : Fin hW.cover.size)
    (x : BanachSpectrum (a.algebra (hW.cover.index i))) :
    hW.chart ((hW.componentDomain i).spectrumMap x) =
      a.chart (hW.cover.index i) x :=
  W.chart_component hW.affinoid hW.bijective hW.cover hW.cover_locus i x

end IsRecognized

variable (a)

/-- Intrinsic affinoidness of original-chart sections follows from the
constructed bounded recovery of the entire original chart algebra. -/
theorem original_isAffinoid (parent : a.Index) :
    IsAffinoidAlgebra K (original a parent).SectionAlgebra :=
  (PresentedAffinoidAlgebra.isAffinoidAlgebra K (a.algebra parent)).of_boundedEquiv
    (originalAlgebraEquiv a parent)

/-- For an original chart the already constructed canonical map is
bijective, by its full original-algebra recovery formula. -/
theorem original_spectrumMap_bijective (parent : a.Index) :
    Function.Bijective (original a parent).spectrumMap := by
  let e := (a.isEmbedding_chart parent).toHomeomorph
  have heq : (fun x => (original a parent).spectrumMap x) =
      (originalAlgebraEquiv a parent).spectrumHomeomorph.symm ∘ e.symm := by
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change (original a parent).spectrumMap (e y) =
      (originalAlgebraEquiv a parent).spectrumHomeomorph.symm (e.symm (e y))
    rw [e.symm_apply_apply]
    exact (original_spectrumMap a parent y).symm
  change Function.Bijective (fun x => (original a parent).spectrumMap x)
  rw [heq]
  exact (originalAlgebraEquiv a parent).spectrumHomeomorph.symm.bijective.comp
    e.symm.bijective

variable {a} in
/-- The canonical comparison to the chosen defining cover is the full
bounded identity, not merely equal on spectrum points. -/
theorem comparisonEquiv_gluingData :
    (W.comparisonEquiv W.gluingData W.gluingData_locus).toBoundedAlgHom =
      BoundedAlgHom.id K W.SectionAlgebra :=
  W.gluingData.restrictionTo_self

variable {a} in
theorem componentRestriction_gluingData (h : IsAffinoidAlgebra K W.SectionAlgebra)
    (i : Fin W.gluingData.size) :
    W.componentRestriction h W.gluingData W.gluingData_locus i =
      (W.gluingData.projection i).comp h.presentationEquiv.toBoundedAlgHom := by
  unfold componentRestriction
  rw [W.comparisonEquiv_gluingData, BoundedAlgHom.comp_id]

/-- The recognized original chart is the original chart composed with the
constructed bounded original-algebra/presentation comparison. -/
theorem original_chart (parent : a.Index)
    (h : IsAffinoidAlgebra K (original a parent).SectionAlgebra)
    (hb : Function.Bijective (original a parent).spectrumMap)
    (x : BanachSpectrum h.presentation) :
    (original a parent).chart h hb x =
      a.chart parent
        (((originalAlgebraEquiv a parent).trans h.presentationEquiv.symm).spectrumHomeomorph
          x) := by
  let e := (originalAlgebraEquiv a parent).trans h.presentationEquiv.symm
  let y : (original a parent).val :=
    ⟨a.chart parent (e.spectrumHomeomorph x), Set.mem_range_self _⟩
  have hy : (original a parent).coordinates h hb y = x := by
    change h.presentationEquiv.spectrumHomeomorph ((original a parent).spectrumMap y) = x
    rw [← original_spectrumMap a parent (e.spectrumHomeomorph x)]
    apply BanachSpectrum.ext
    intro b
    change x (h.presentationEquiv.symm
      ((originalAlgebraEquiv a parent)
        ((originalAlgebraEquiv a parent).symm (h.presentationEquiv b)))) = x b
    rw [(originalAlgebraEquiv a parent).apply_symm_apply,
      h.presentationEquiv.symm_apply_apply]
  have hxy : ((original a parent).coordinates h hb).symm x = y := by
    apply ((original a parent).coordinates h hb).injective
    exact (((original a parent).coordinates h hb).apply_symm_apply x).trans hy.symm
  exact congrArg Subtype.val hxy

theorem original_componentRestriction (parent : a.Index)
    (h : IsAffinoidAlgebra K (original a parent).SectionAlgebra)
    (i : Fin (original a parent).gluingData.size) :
    (original a parent).componentRestriction h (original a parent).gluingData
        (original a parent).gluingData_locus i =
      (a.restriction ((original a parent).gluingData.index i) parent
        ((original a parent).gluingData.member_subset_parent parent
          (original a parent).gluingData_locus i)).comp
        (((originalAlgebraEquiv a parent).trans h.presentationEquiv.symm).symm.toBoundedAlgHom) := by
  rw [(original a parent).componentRestriction_gluingData h i]
  apply BoundedAlgHom.ext
  intro b
  exact (congrArg
    (fun f : BoundedAlgHom K (original a parent).SectionAlgebra
      (a.algebra ((original a parent).gluingData.index i)) => f (h.presentationEquiv b))
    ((original a parent).gluingData.restriction_comp_glueToParent parent
      (original a parent).gluingData_locus i)).symm

/-- Every original chart satisfies all three recognition conditions.
Full domain representation follows by transporting each original
restriction along the actually constructed bounded base equivalence. -/
theorem original_isRecognized (parent : a.Index) :
    (original a parent).IsRecognized := by
  let W := original a parent
  let h := original_isAffinoid a parent
  let hb := original_spectrumMap_bijective a parent
  let e := (originalAlgebraEquiv a parent).trans h.presentationEquiv.symm
  refine ⟨h, hb, W.gluingData, W.gluingData_locus, W.gluingData_isSpecial, ?_⟩
  intro i
  rw [original_componentRestriction a parent h i]
  have hl : W.chart h hb ⁻¹' Set.range (a.chart (W.gluingData.index i)) =
      e.spectrumHomeomorph ⁻¹'
        (a.chart parent ⁻¹' Set.range (a.chart (W.gluingData.index i))) := by
    ext x
    change W.chart h hb x ∈ Set.range (a.chart (W.gluingData.index i)) ↔
      a.chart parent (e.spectrumHomeomorph x) ∈ Set.range (a.chart (W.gluingData.index i))
    rw [original_chart a parent h hb x]
  rw [hl]
  exact (a.restriction_represents (W.gluingData.index i) parent
    (W.gluingData.member_subset_parent parent W.gluingData_locus i)).precomp_equiv e

end Langlands.Analytic.IndexedAffinoidAtlas.SpecialSubset
