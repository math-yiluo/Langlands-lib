import Langlands.Geometry.Analytic.RationalSpectrumAtlas
import Langlands.Geometry.Analytic.AtlasAffinoidDomainExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph
import Langlands.Geometry.Analytic.AtlasTopology.IntersectionNets

/-! # Rational cuts of an affinoid atlas with a greatest chart -/

noncomputable section

universe u v w

namespace Langlands.Analytic.RationalCutAtlas

open CategoryTheory Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (t : a.Index)

/-- Intersect an original chart with an actual rational locus in the greatest chart. -/
def cut (i : a.Index) (d : RationalChart K (a.algebra t)) : Set X :=
  Set.range (a.chart i) ∩ a.chart t '' d.locus

/-- Literal ambient loci prevent duplicate chart domains. -/
def Index := {U : Set X // ∃ i : a.Index, ∃ d : RationalChart K (a.algebra t),
  cut a t i d = U}

namespace Index

def ofCut (i : a.Index) (d : RationalChart K (a.algebra t)) : Index a t :=
  ⟨cut a t i d, i, d, rfl⟩

/-- The original locus is obtained by cutting with the whole rational locus. -/
def ofOriginal (i : a.Index) : Index a t :=
  ofCut a t i (RationalChart.whole K (a.algebra t))

/-- Every rational locus in the greatest chart is among the cuts. -/
def ofRational (d : RationalChart K (a.algebra t)) : Index a t :=
  ofCut a t t d

def original (s : Index a t) : a.Index := s.property.choose

def rational (s : Index a t) : RationalChart K (a.algebra t) :=
  s.property.choose_spec.choose

@[simp]
theorem cut_original_rational (s : Index a t) :
    cut a t (s.original a t) (s.rational a t) = s.val :=
  s.property.choose_spec.choose_spec

end Index

/-- The family of all the specified cuts, with no chosen quotient in its definition. -/
def family : Set (Set X) := Set.range (fun s : Index a t => s.val)

variable (ht : ∀ i, Set.range (a.chart i) ⊆ Set.range (a.chart t))

include ht in
@[simp]
theorem cut_whole (i : a.Index) :
    cut a t i (RationalChart.whole K (a.algebra t)) = Set.range (a.chart i) := by
  rw [cut, RationalChart.locus_whole, Set.image_univ]
  exact Set.inter_eq_left.mpr (ht i)

@[simp]
theorem cut_greatest (d : RationalChart K (a.algebra t)) :
    cut a t t d = a.chart t '' d.locus := by
  apply Set.inter_eq_right.mpr
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

include ht in
@[simp]
theorem Index.val_ofOriginal (i : a.Index) :
    (Index.ofOriginal a t i).val = Set.range (a.chart i) :=
  cut_whole a t ht i

@[simp]
theorem Index.val_ofRational (d : RationalChart K (a.algebra t)) :
    (Index.ofRational a t d).val = a.chart t '' d.locus :=
  cut_greatest a t d

include ht in
/-- The net covers X, so the greatest chart covers X. -/
theorem greatest_chart_surjective : Function.Surjective (a.chart t) := by
  intro x
  have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (a.chart i)) := by
    rw [a.isNet_chartFamily.1.covers]
    exact Set.mem_univ x
  obtain ⟨_, ⟨i, rfl⟩, hx⟩ := hx
  exact ht i hx

/-- The existing greatest-chart map, equipped with its proved inverse. -/
def greatestChartHomeomorph : BanachSpectrum (a.algebra t) ≃ₜ X :=
  (a.isEmbedding_chart t).toHomeomorphOfSurjective (greatest_chart_surjective a t ht)

@[simp]
theorem greatestChartHomeomorph_apply (x : BanachSpectrum (a.algebra t)) :
    greatestChartHomeomorph a t ht x = a.chart t x := rfl

theorem family_eq_intersectionFamily : family a t =
    AtlasTopology.intersectionFamily (Set.range (fun i => Set.range (a.chart i)))
      (AtlasTopology.imageFamily (greatestChartHomeomorph a t ht)
        (RationalSpectrumAtlas.family K (a.algebra t))) := by
  ext U
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, d, hs⟩ := s.property
    refine ⟨Set.range (a.chart i), ⟨i, rfl⟩, a.chart t '' d.locus, ?_, hs.symm⟩
    refine ⟨d.locus, ?_, rfl⟩
    rw [RationalSpectrumAtlas.family_eq_range_locus]
    exact ⟨d, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨V, hV, rfl⟩, rfl⟩
    rw [RationalSpectrumAtlas.family_eq_range_locus] at hV
    obtain ⟨d, rfl⟩ := hV
    exact ⟨Index.ofCut a t i d, rfl⟩

include ht in
/-- Its topology comes from intersecting the original and transported rational nets. -/
theorem isNet_family : AtlasTopology.IsNet (family a t) := by
  rw [family_eq_intersectionFamily a t ht]
  exact a.isNet_chartFamily.intersectionFamily
    ((RationalSpectrumAtlas.isNet_family (K := K) (A := a.algebra t)).imageFamily
      (greatestChartHomeomorph a t ht))

/-- The actual positive-radius rational quotient over the original smaller chart. -/
def pullbackChart (i : a.Index) (d : RationalChart K (a.algebra t)) :
    RationalChart K (a.algebra i) :=
  RationalChart.pullback (a.restriction i t (ht i)) d

/-- Retain the rational quotient algebra and compose its structural map to the
common base; full representation is proved by the existing extension construction. -/
def cutDomain (i : a.Index) (d : RationalChart K (a.algebra t)) :
    Domain K (a.algebra t) :=
  a.extendDomain i t (ht i) (pullbackChart a t ht i d).toDomain

theorem chart_image_cutDomain_locus (i : a.Index)
    (d : RationalChart K (a.algebra t)) :
    a.chart t '' (cutDomain a t ht i d).locus = cut a t i d := by
  rw [cutDomain, a.chart_image_extendDomain_locus]
  change a.chart i '' (pullbackChart a t ht i d).locus = _
  rw [pullbackChart, RationalChart.pullback_locus]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, _, hy, a.restriction_chart i t (ht i) y⟩
  · rintro ⟨⟨y, rfl⟩, z, hz, hzy⟩
    refine ⟨y, ?_, rfl⟩
    change BanachSpectrum.comap (a.restriction i t (ht i)).toBoundedRingHom y ∈ d.locus
    have heq := (a.isEmbedding_chart t).injective
      ((a.restriction_chart i t (ht i) y).trans hzy.symm)
    exact heq.symm ▸ hz

theorem cutDomain_spectrumMap (i : a.Index) (d : RationalChart K (a.algebra t))
    (x : BanachSpectrum (cutDomain a t ht i d).algebra) :
    (cutDomain a t ht i d).spectrumMap x =
      BanachSpectrum.comap (a.restriction i t (ht i)).toBoundedRingHom
        ((pullbackChart a t ht i d).spectrumMap x) := by
  apply BanachSpectrum.ext
  intro b
  rfl

theorem isEmbedding_cutDomain_spectrumMap (i : a.Index)
    (d : RationalChart K (a.algebra t)) :
    IsEmbedding (cutDomain a t ht i d).spectrumMap := by
  have heq : ⇑(cutDomain a t ht i d).spectrumMap =
      BanachSpectrum.comap (a.restriction i t (ht i)).toBoundedRingHom ∘
        (pullbackChart a t ht i d).spectrumMap :=
    funext (cutDomain_spectrumMap a t ht i d)
  rw [heq]
  exact (a.isEmbedding_restriction i t (ht i)).comp
    (((pullbackChart a t ht i d).spectrumMap.continuous.isClosedEmbedding
      (pullbackChart a t ht i d).spectrumMap_injective).isEmbedding)

namespace Index

/-- A chosen actual full-domain presentation over the common greatest-chart algebra. -/
def domain (s : Index a t) : Domain K (a.algebra t) :=
  cutDomain a t ht (s.original a t) (s.rational a t)

theorem chart_image_domain_locus (s : Index a t) :
    a.chart t '' (s.domain a t ht).locus = s.val :=
  (chart_image_cutDomain_locus a t ht _ _).trans (s.cut_original_rational a t)

/-- The common-base locus is exactly the ambient literal locus in chart coordinates. -/
theorem domain_locus_eq_preimage (s : Index a t) :
    (s.domain a t ht).locus = a.chart t ⁻¹' s.val := by
  rw [← s.chart_image_domain_locus a t ht]
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    exact (a.isEmbedding_chart t).injective heq ▸ hy

end Index

/-- The chart is the actual structural spectrum map followed by the original chart. -/
def chart (s : Index a t) : BanachSpectrum (s.domain a t ht).algebra → X :=
  a.chart t ∘ (s.domain a t ht).spectrumMap

@[simp]
theorem range_chart (s : Index a t) : Set.range (chart a t ht s) = s.val := by
  rw [chart, Set.range_comp]
  change a.chart t '' Set.range
    (BanachSpectrum.comap (s.domain a t ht).baseMap.toBoundedRingHom) = s.val
  rw [(s.domain a t ht).represents.2.1]
  exact s.chart_image_domain_locus a t ht

theorem isEmbedding_chart (s : Index a t) : IsEmbedding (chart a t ht s) :=
  (a.isEmbedding_chart t).comp (isEmbedding_cutDomain_spectrumMap a t ht _ _)

theorem chartDomain_injective :
    Function.Injective (fun s : Index a t => Set.range (chart a t ht s)) := by
  intro s r h
  apply Subtype.ext
  simpa only [range_chart] using h

/-- Ambient containment descends through the injective greatest-chart map. -/
theorem domain_locus_subset (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r)) :
    (s.domain a t ht).locus ⊆ (r.domain a t ht).locus := by
  intro x hx
  have hmem : a.chart t x ∈ Set.range (chart a t ht s) := by
    rw [range_chart, ← s.chart_image_domain_locus a t ht]
    exact ⟨x, hx, rfl⟩
  have hr := h hmem
  rw [range_chart, ← r.chart_image_domain_locus a t ht] at hr
  obtain ⟨y, hy, heq⟩ := hr
  exact (a.isEmbedding_chart t).injective heq ▸ hy

/-- The bounded restriction is constructed from the full domain representation. -/
def inclusion (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r)) :
    s.domain a t ht ⟶ r.domain a t ht :=
  Domain.inclusionOfSubset _ _ (domain_locus_subset a t ht s r h)

def restriction (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r)) :
    BoundedAlgHom K (r.domain a t ht).algebra (s.domain a t ht).algebra :=
  (inclusion a t ht s r h).restriction

theorem restriction_comp_baseMap (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r)) :
    (restriction a t ht s r h).comp (r.domain a t ht).baseMap =
      (s.domain a t ht).baseMap :=
  (inclusion a t ht s r h).comp_baseMap

theorem restriction_chart (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r))
    (x : BanachSpectrum (s.domain a t ht).algebra) :
    chart a t ht r (BanachSpectrum.comap (restriction a t ht s r h).toBoundedRingHom x) =
      chart a t ht s x :=
  congrArg (a.chart t) ((inclusion a t ht s r h).spectrumMap_over_base x)

/-- Full relative factorization and uniqueness are consequences of the two
representations over the common base, including equality of whole bounded maps. -/
theorem restriction_universal (s r : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r))
    (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (r.domain a t ht).algebra R)
    (hφ : ∀ x : BanachSpectrum R,
      chart a t ht r (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        Set.range (chart a t ht s)) :
    ∃! ψ : BoundedAlgHom K (s.domain a t ht).algebra R,
      ψ.comp (restriction a t ht s r h) = φ := by
  have hbase : HasImageIn K (φ.comp (r.domain a t ht).baseMap)
      (s.domain a t ht).locus := by
    intro x
    have hx := hφ x
    rw [range_chart, ← s.chart_image_domain_locus a t ht] at hx
    obtain ⟨y, hy, heq⟩ := hx
    change BanachSpectrum.comap
      (φ.toBoundedRingHom.comp (r.domain a t ht).baseMap.toBoundedRingHom) x ∈ _
    rw [BanachSpectrum.comap_comp]
    have hxy := (a.isEmbedding_chart t).injective heq
    change y = BanachSpectrum.comap (r.domain a t ht).baseMap.toBoundedRingHom
      (BanachSpectrum.comap φ.toBoundedRingHom x) at hxy
    exact hxy ▸ hy
  obtain ⟨ψ, hψ, huniq⟩ := (s.domain a t ht).represents.2.2 R
    (φ.comp (r.domain a t ht).baseMap) hbase
  refine ⟨ψ, ?_, ?_⟩
  · apply ((r.domain a t ht).represents.2.2 R
      (φ.comp (r.domain a t ht).baseMap)
      (fun x => (r.domain a t ht).represents.hasImageIn
        (BanachSpectrum.comap φ.toBoundedRingHom x))).unique
    · rw [BoundedAlgHom.comp_assoc, restriction_comp_baseMap, hψ]
    · rfl
  · intro ψ' hψ'
    apply huniq ψ'
    calc
      ψ'.comp (s.domain a t ht).baseMap =
          (ψ'.comp (restriction a t ht s r h)).comp (r.domain a t ht).baseMap := by
            rw [BoundedAlgHom.comp_assoc, restriction_comp_baseMap]
      _ = φ.comp (r.domain a t ht).baseMap := by rw [hψ']

theorem restriction_id (s : Index a t)
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht s)) :
    restriction a t ht s s h = BoundedAlgHom.id K (s.domain a t ht).algebra :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (s.domain a t ht) (s.domain a t ht))
      inferInstance (inclusion a t ht s s h) (𝟙 (s.domain a t ht)))

theorem restriction_comp (s r q : Index a t)
    (hsr : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r))
    (hrq : Set.range (chart a t ht r) ⊆ Set.range (chart a t ht q))
    (hsq : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht q)) :
    restriction a t ht s q hsq =
      (restriction a t ht s r hsr).comp (restriction a t ht r q hrq) :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (s.domain a t ht) (q.domain a t ht))
      inferInstance (inclusion a t ht s q hsq)
      (inclusion a t ht s r hsr ≫ inclusion a t ht r q hrq))

/-- An actual enlargement by the rational cuts in a greatest original chart. -/
def atlas : IndexedAffinoidAtlas.{u, v, v} K X where
  Index := Index a t
  algebra s := (s.domain a t ht).algebra
  chart := chart a t ht
  isEmbedding_chart := isEmbedding_chart a t ht
  chartDomain_injective := chartDomain_injective a t ht
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := by
    simpa only [family, range_chart] using isNet_family a t ht
  restriction := restriction a t ht
  restriction_chart := restriction_chart a t ht
  restriction_universal := restriction_universal a t ht
  restriction_id := restriction_id a t ht
  restriction_comp := restriction_comp a t ht

/-- The resulting net is precisely the rational-cut family. -/
theorem atlas_chartFamily :
    Set.range (fun s => Set.range ((atlas a t ht).chart s)) = family a t := by
  change Set.range (fun s : Index a t => Set.range (chart a t ht s)) = family a t
  simp only [range_chart, family]

/-- Each original literal chart locus is retained. -/
theorem atlas_ofOriginal_range (i : a.Index) :
    Set.range ((atlas a t ht).chart (Index.ofOriginal a t i)) =
      Set.range (a.chart i) :=
  (range_chart a t ht _).trans (Index.val_ofOriginal a t ht i)

/-- All ambient rational loci occur as literal chart ranges. -/
theorem atlas_ofRational_range (d : RationalChart K (a.algebra t)) :
    Set.range ((atlas a t ht).chart (Index.ofRational a t d)) =
      a.chart t '' d.locus :=
  (range_chart a t ht _).trans (Index.val_ofRational a t d)

theorem original_domain_locus (i : a.Index) :
    (a.restrictionDomain i t (ht i)).locus =
      ((Index.ofOriginal a t i).domain a t ht).locus := by
  rw [Index.domain_locus_eq_preimage, Index.val_ofOriginal a t ht]
  rfl

/-- The chosen presentation at an original locus is boundedly equivalent to
the original algebra, over the greatest-chart algebra. -/
def originalAlgebraEquiv (i : a.Index) :
    BoundedAlgEquiv K (a.algebra i) ((atlas a t ht).algebra (Index.ofOriginal a t i)) :=
  Domain.boundedEquivOfLocusEq (a.restrictionDomain i t (ht i))
    ((Index.ofOriginal a t i).domain a t ht) (original_domain_locus a t ht i)

theorem originalAlgebraEquiv_comp_restriction (i : a.Index) :
    (originalAlgebraEquiv a t ht i).toBoundedAlgHom.comp (a.restriction i t (ht i)) =
      ((Index.ofOriginal a t i).domain a t ht).baseMap :=
  Domain.boundedEquivOfLocusEq_comp_baseMap _ _ (original_domain_locus a t ht i)

/-- The bounded comparison induces a homeomorphism of the actual chart spectra. -/
def originalSpectrumHomeomorph (i : a.Index) :
    BanachSpectrum (a.algebra i) ≃ₜ
      BanachSpectrum ((atlas a t ht).algebra (Index.ofOriginal a t i)) :=
  Domain.spectrumHomeomorphOfLocusEq (a.restrictionDomain i t (ht i))
    ((Index.ofOriginal a t i).domain a t ht) (original_domain_locus a t ht i)

theorem originalSpectrumHomeomorph_chart (i : a.Index)
    (x : BanachSpectrum (a.algebra i)) :
    (atlas a t ht).chart (Index.ofOriginal a t i)
      (originalSpectrumHomeomorph a t ht i x) = a.chart i x := by
  have h := Domain.spectrumHomeomorphOfLocusEq_over_base
    (a.restrictionDomain i t (ht i)) ((Index.ofOriginal a t i).domain a t ht)
    (original_domain_locus a t ht i) x
  exact (congrArg (a.chart t) h).trans (a.restriction_chart i t (ht i) x)

end Langlands.Analytic.RationalCutAtlas
