import Langlands.Geometry.Analytic.FinitePieceChartMaps
import Langlands.Geometry.Analytic.RecognizedContainedMap
import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessStatement

/-! # Coordinate maps into recognized affinoid algebras of an affine analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.FinitePieceLocal

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas

/-- Elements of a recognized algebra are determined by their original restrictions. -/
theorem recognized_algebra_ext {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X : Type v} [TopologicalSpace X]
    {a : IndexedAffinoidAtlas.{u, v, w} K X} (W : a.RecognizedSubset) {x y : W.algebra}
    (h : ∀ k (hk : range (a.chart k) ⊆ W.locus),
      W.originalRestriction k hk x = W.originalRestriction k hk y) : x = y := by
  apply W.componentCover.algebra_ext_of_restrict_eq
  intro i
  let i' : Fin W.property.cover.size := i
  have e := W.componentDomain_baseMap i'
  change (W.property.componentDomain i').baseMap x = (W.property.componentDomain i').baseMap y
  rw [e]
  exact h _ _

theorem isCompact_recognized_locus {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X : Type v} [TopologicalSpace X]
    {a : IndexedAffinoidAtlas.{u, v, w} K X} (W : a.RecognizedSubset) : IsCompact W.locus :=
  W.range_chart ▸ isCompact_range W.isEmbedding_chart.continuous

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- A compact subset of the analytification lies in all sufficiently large original
saturated charts. -/
theorem exists_orig_superset {Z : Set (Space K P)} (hZ : IsCompact Z) :
    ∃ m₀, ∀ m, m₀ ≤ m →
      Z ⊆ range ((presentation K P).atlas.saturatedAtlas.chart
        (origIndex P (representative K P m))) := by
  obtain ⟨m₀, hm₀⟩ := exists_chart_superset P hZ
  exact ⟨m₀, fun m hm => (range_origIndex_representative P m).symm ▸ hm₀ m hm⟩

/-- The coordinate map of `A` into a recognized algebra, through a saturated chart
containing its locus. -/
def recMap (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j)) :
    A →ₐ[K] W.algebra :=
  (W.containedRestriction j hW).toAlgHom.comp (satMap P j)

theorem recMap_apply (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j)) (a : A) :
    recMap P W j hW a = W.containedRestriction j hW (satMap P j a) :=
  rfl

theorem originalRestriction_recMap (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j))
    (k : (presentation K P).atlas.saturatedAtlas.Index)
    (hk : range ((presentation K P).atlas.saturatedAtlas.chart k) ⊆ W.locus) (a : A) :
    W.originalRestriction k hk (recMap P W j hW a) = satMap P k a := by
  have e := congrArg (fun q => q (satMap P j a))
    (W.originalRestriction_comp_containedRestriction j hW k hk)
  exact e.trans (satMap_restriction P k j _ a)

/-- The coordinate map does not depend on the chosen chart. -/
theorem recMap_eq (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j j' : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j))
    (hW' : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j')) :
    recMap P W j hW = recMap P W j' hW' := by
  ext a
  apply recognized_algebra_ext W
  intro k hk
  rw [originalRestriction_recMap, originalRestriction_recMap]

/-- Every point of the recognized algebra restricts along the coordinate map to the
seminorm of its image point. -/
theorem recMap_pointSeminorm (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j))
    (t : BanachSpectrum W.algebra) (a : A) :
    t (recMap P W j hW a) = pointSeminorm K P (W.chart t) a := by
  let L := (presentation K P).atlas.saturatedRepresentative j
  let y := BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom t
  have e1 : affinoidBaseMap K P L.algebra (LocalDomainMaps.localAlgebraMap P L) y =
      L.ambientMap y :=
    LocalDomainMaps.affinoidBaseMap_localAlgebraMap P L y
  have e2 := LocalDomainMaps.pointSeminorm_affinoidBaseMap P L.algebra
    (LocalDomainMaps.localAlgebraMap P L) y a
  rw [← W.chart_containedRestriction j hW t]
  change _ = pointSeminorm K P (L.ambientMap y) a
  rw [← e1, e2]
  rfl

/-- The coordinate map is flat, given flatness of the chart algebras and of the
structural maps of affinoid domains. -/
theorem recMap_flat (hchart : AffineAnalytificationChartFlatStatement.{u, v})
    (hdom : Domain.FlatnessStatement.{u})
    (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j)) :
    (recMap P W j hW).toRingHom.Flat := by
  have h1 := hchart K A P ((presentation K P).atlas.saturatedRepresentative j).index.val
  have h2 := hdom K _ ((presentation K P).atlas.saturatedRepresentative j).domain
  have h3 := hdom K _ (W.containedDomain j hW)
  exact (h1.comp h2).comp h3

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The bounded map of a piece carries the coordinate map of `A` to the coordinate map
of `B` composed with `f`. -/
theorem pullback_recMap (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
    (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (h : (saturatedHom K P Q f).baseMap '' range V'.chart ⊆ range W.chart)
    (i : (presentation K Q).atlas.saturatedAtlas.Index)
    (j : (presentation K P).atlas.saturatedAtlas.Index)
    (hV : V'.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j))
    (hij : (saturatedHom K P Q f).baseMap ''
        range ((presentation K Q).atlas.saturatedAtlas.chart i) ⊆
      range ((presentation K P).atlas.saturatedAtlas.chart j)) (a : A) :
    (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h (recMap P W j hW a) =
      recMap Q V' i hV (f a) := by
  have e := congrArg (fun q => q (satMap P j a))
    ((saturatedHom K P Q f).fullRecognitionPairs_comp_containedRestriction
      (A := presentation K Q) (B := presentation K P) V' W i j hV hW hij h)
  exact e.trans (congrArg (V'.containedRestriction i hV)
    (LocalDomainMaps.saturatedHom_pullback_localAlgebraMap P Q f i j hij a))

end Langlands.Analytic.AffineAnalytification.FinitePieceLocal
