import Langlands.Geometry.Analytic.DirectedAtlasDomainCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # Rational enlargement of an atlas with directed original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.DirectedRationalAtlas

open CategoryTheory Set Filter Topology PresentedAffinoidAlgebra
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A rational locus in any original chart, viewed in the ambient space. -/
def locus (i : a.Index) (d : RationalChart K (a.algebra i)) : Set X :=
  a.chart i '' d.locus

/-- Literal ambient loci identify repeated rational presentations. -/
def Index := {U : Set X // ∃ i : a.Index, ∃ d : RationalChart K (a.algebra i),
  locus a i d = U}

namespace Index

def ofChart (i : a.Index) (d : RationalChart K (a.algebra i)) : Index a :=
  ⟨locus a i d, i, d, rfl⟩

def ofOriginal (i : a.Index) : Index a :=
  ofChart a i (RationalChart.whole K (a.algebra i))

def original (s : Index a) : a.Index := s.property.choose

def rational (s : Index a) : RationalChart K (a.algebra (s.original a)) :=
  s.property.choose_spec.choose

@[simp]
theorem locus_original_rational (s : Index a) :
    locus a (s.original a) (s.rational a) = s.val :=
  s.property.choose_spec.choose_spec

@[simp]
theorem val_ofOriginal (i : a.Index) :
    (ofOriginal a i).val = Set.range (a.chart i) := by
  change a.chart i '' (RationalChart.whole K (a.algebra i)).locus = _
  rw [RationalChart.locus_whole, Set.image_univ]

end Index

/-- All local rational loci; the definition chooses no quotient presentation. -/
def family : Set (Set X) := Set.range (fun s : Index a => s.val)

theorem originalFamily_subset :
    Set.range (fun i => Set.range (a.chart i)) ⊆ family a := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Index.ofOriginal a i, Index.val_ofOriginal a i⟩

/-- Original bounded restrictions pull rational inequalities back exactly. -/
theorem chart_image_pullback (k i : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (d : RationalChart K (a.algebra i)) :
    locus a k (RationalChart.pullback (a.restriction k i hki) d) =
      Set.range (a.chart k) ∩ locus a i d := by
  rw [locus, RationalChart.pullback_locus]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, _, hy, a.restriction_chart k i hki y⟩
  · rintro ⟨⟨y, rfl⟩, z, hz, hzy⟩
    refine ⟨y, ?_, rfl⟩
    change BanachSpectrum.comap (a.restriction k i hki).toBoundedRingHom y ∈ d.locus
    have heq := (a.isEmbedding_chart i).injective
      ((a.restriction_chart k i hki y).trans hzy.symm)
    exact heq.symm ▸ hz

/-- Intersecting two local rational loci on any contained original chart gives
an actual rational presentation over that chart's original algebra. -/
theorem chart_image_inter_pullback (k i j : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (d : RationalChart K (a.algebra i)) (e : RationalChart K (a.algebra j)) :
    locus a k ((RationalChart.pullback (a.restriction k i hki) d).inter
      (RationalChart.pullback (a.restriction k j hkj) e)) =
      Set.range (a.chart k) ∩ (locus a i d ∩ locus a j e) := by
  have hinj := (a.isEmbedding_chart k).injective
  calc
    _ = locus a k (RationalChart.pullback (a.restriction k i hki) d) ∩
        locus a k (RationalChart.pullback (a.restriction k j hkj) e) := by
      simp only [locus, RationalChart.locus_inter, Set.image_inter hinj]
    _ = _ := by
      rw [chart_image_pullback, chart_image_pullback]
      ext x
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.2⟩,
        fun h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩⟩

/-- The finite original overlap neighborhoods, cut by both rational loci,
prove the net axiom. Directedness is unnecessary for this topological step. -/
theorem isNet_family : AtlasTopology.IsNet (family a) := by
  refine ⟨a.isNet_chartFamily.1.mono (originalFamily_subset a), ?_⟩
  rintro S ⟨s, rfl⟩ T ⟨t, rfl⟩
  obtain ⟨i, d, hs⟩ := s.property
  obtain ⟨j, e, ht⟩ := t.property
  change AtlasTopology.IsQuasinet (AtlasTopology.restrictedFamily (family a) (s.val ∩ t.val))
  rw [← hs, ← ht]
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  intro U hU x hx
  have hU' := Set.mem_singleton_iff.mp hU
  subst U
  have hsub : locus a i d ∩ locus a j e ⊆
      Set.range (a.chart i) ∩ Set.range (a.chart j) := by
    rintro _ ⟨⟨y, _, hy⟩, z, _, hz⟩
    exact ⟨⟨y, hy⟩, z, hz⟩
  obtain ⟨σ, hf, hsσ, hm, hn⟩ :=
    a.isNet_chartFamily.locallyRefines_intersectionFamily
      (Set.range (a.chart i) ∩ Set.range (a.chart j))
      ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ x (hsub hx)
  let δ : Set (Set X) := (fun V => V ∩ (locus a i d ∩ locus a j e)) '' σ
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro V ⟨W, hW, rfl⟩
    obtain ⟨k, rfl⟩ := hsσ hW
    have hki := (hm _ hW).1.trans Set.inter_subset_left
    have hkj := (hm _ hW).1.trans Set.inter_subset_right
    exact ⟨Index.ofChart a k
      ((RationalChart.pullback (a.restriction k i hki) d).inter
        (RationalChart.pullback (a.restriction k j hkj) e)),
      chart_image_inter_pullback a k i j hki hkj d e⟩
  · rintro V ⟨W, hW, rfl⟩
    exact ⟨Set.inter_subset_right, (hm W hW).2, hx⟩
  · have heq : ⋃₀ δ = (⋃₀ σ) ∩ (locus a i d ∩ locus a j e) := by
      ext y
      constructor
      · rintro ⟨_, ⟨W, hW, rfl⟩, hy⟩
        exact ⟨⟨W, hW, hy.1⟩, hy.2⟩
      · rintro ⟨⟨W, hW, hy⟩, hz⟩
        exact ⟨_, ⟨W, hW, rfl⟩, hy, hz⟩
    rw [heq]
    exact inter_mem ((nhdsWithin_mono x hsub) hn) self_mem_nhdsWithin

variable (hd : a.HasDirectedCharts)

/-- Full relative factorization follows by extension of both domains to one
common original upper chart. No domain-spectrum injectivity is assumed. -/
theorem inclusion_universal {U V : IndexedAffinoidAtlas.DirectedDomain a hd}
    (f : U ⟶ V) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K V.algebra R)
    (hφ : ∀ x : BanachSpectrum R,
      V.ambientMap (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ U.locus) :
    ∃! ψ : BoundedAlgHom K U.algebra R, ψ.comp f.restriction = φ := by
  obtain ⟨q, hUq, hVq⟩ := hd U.index V.index
  let Uq := a.extendDomain U.index q hUq U.domain
  let Vq := a.extendDomain V.index q hVq V.domain
  have hbase : HasImageIn K (φ.comp Vq.baseMap) Uq.locus := by
    intro x
    have hx := hφ x
    change V.ambientMap (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
      a.chart U.index '' U.domain.locus at hx
    rw [← a.chart_image_extendDomain_locus U.index q hUq U.domain] at hx
    obtain ⟨y, hy, heq⟩ := hx
    have hchart : a.chart q (BanachSpectrum.comap
        (φ.comp Vq.baseMap).toBoundedRingHom x) =
        V.ambientMap (BanachSpectrum.comap φ.toBoundedRingHom x) := by
      change a.chart q (BanachSpectrum.comap
        (φ.toBoundedRingHom.comp (V.domain.baseMap.toBoundedRingHom.comp
          (a.restriction V.index q hVq).toBoundedRingHom)) x) = _
      rw [BanachSpectrum.comap_comp, BanachSpectrum.comap_comp]
      exact a.restriction_chart V.index q hVq _
    exact (a.isEmbedding_chart q).injective (heq.trans hchart.symm) ▸ hy
  obtain ⟨ψ, hψ, huniq⟩ := Uq.represents.2.2 R (φ.comp Vq.baseMap) hbase
  change BoundedAlgHom K U.algebra R at ψ
  change ψ.comp (U.domain.baseMap.comp (a.restriction U.index q hUq)) =
    φ.comp (V.domain.baseMap.comp (a.restriction V.index q hVq)) at hψ
  have hf := f.comp_baseMap q hUq hVq
  refine ⟨ψ, ?_, ?_⟩
  · apply (Vq.represents.2.2 R (φ.comp Vq.baseMap)
      (fun x => Vq.represents.hasImageIn
        (BanachSpectrum.comap φ.toBoundedRingHom x))).unique
    · change (ψ.comp f.restriction).comp
        (V.domain.baseMap.comp (a.restriction V.index q hVq)) =
          φ.comp (V.domain.baseMap.comp (a.restriction V.index q hVq))
      rw [BoundedAlgHom.comp_assoc, hf, hψ]
    · rfl
  · intro ψ' hψ'
    apply huniq ψ'
    change ψ'.comp (U.domain.baseMap.comp (a.restriction U.index q hUq)) =
      φ.comp (V.domain.baseMap.comp (a.restriction V.index q hVq))
    rw [← hf, ← BoundedAlgHom.comp_assoc, hψ']

namespace Index

/-- The chosen actual rational quotient, retained as a full represented domain
in its chosen original chart. -/
def directedDomain (s : Index a) : IndexedAffinoidAtlas.DirectedDomain a hd :=
  ⟨s.original a, (s.rational a).toDomain⟩

@[simp]
theorem directedDomain_locus (s : Index a) :
    (s.directedDomain a hd).locus = s.val :=
  s.locus_original_rational a

end Index

/-- Compose the actual rational structural spectrum map with the original chart. -/
def chart (s : Index a) : BanachSpectrum (s.rational a).algebra → X :=
  a.chart (s.original a) ∘ (s.rational a).spectrumMap

@[simp]
theorem range_chart (s : Index a) : Set.range (chart a s) = s.val := by
  rw [chart, Set.range_comp]
  change a.chart (s.original a) '' Set.range
    (BanachSpectrum.comap (s.rational a).baseMap.toBoundedRingHom) = s.val
  rw [(s.rational a).represents.2.1]
  exact s.locus_original_rational a

theorem isEmbedding_chart (s : Index a) : IsEmbedding (chart a s) :=
  (a.isEmbedding_chart (s.original a)).comp
    (((s.rational a).spectrumMap.continuous.isClosedEmbedding
      (s.rational a).spectrumMap_injective).isEmbedding)

theorem chartDomain_injective :
    Function.Injective (fun s : Index a => Set.range (chart a s)) := by
  intro s r h
  apply Subtype.ext
  simpa only [range_chart] using h

/-- Directed full-domain factorization constructs the actual bounded inclusion. -/
def inclusion (s r : Index a)
    (h : Set.range (chart a s) ⊆ Set.range (chart a r)) :
    s.directedDomain a hd ⟶ r.directedDomain a hd :=
  IndexedAffinoidAtlas.DirectedDomain.Inclusion.ofSubset _ _ (by
    simpa only [Index.directedDomain_locus, range_chart] using h)

def restriction (s r : Index a)
    (h : Set.range (chart a s) ⊆ Set.range (chart a r)) :
    BoundedAlgHom K (r.rational a).algebra (s.rational a).algebra :=
  (inclusion a hd s r h).restriction

theorem restriction_chart (s r : Index a)
    (h : Set.range (chart a s) ⊆ Set.range (chart a r))
    (x : BanachSpectrum (s.rational a).algebra) :
    chart a r (BanachSpectrum.comap (restriction a hd s r h).toBoundedRingHom x) =
      chart a s x :=
  (inclusion a hd s r h).ambientMap_naturality x

theorem restriction_universal (s r : Index a)
    (h : Set.range (chart a s) ⊆ Set.range (chart a r))
    (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (r.rational a).algebra R)
    (hφ : ∀ x : BanachSpectrum R,
      chart a r (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (chart a s)) :
    ∃! ψ : BoundedAlgHom K (s.rational a).algebra R,
      ψ.comp (restriction a hd s r h) = φ := by
  apply inclusion_universal a hd (inclusion a hd s r h) R φ
  intro x
  change chart a r (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
    (s.directedDomain a hd).locus
  rw [Index.directedDomain_locus, ← range_chart]
  exact hφ x

theorem restriction_id (s : Index a)
    (h : Set.range (chart a s) ⊆ Set.range (chart a s)) :
    restriction a hd s s h = BoundedAlgHom.id K (s.rational a).algebra :=
  congrArg IndexedAffinoidAtlas.DirectedDomain.Inclusion.restriction
    (@Subsingleton.elim (IndexedAffinoidAtlas.DirectedDomain.Inclusion
      (s.directedDomain a hd) (s.directedDomain a hd))
      inferInstance (inclusion a hd s s h) (𝟙 (s.directedDomain a hd)))

theorem restriction_comp (s r q : Index a)
    (hsr : Set.range (chart a s) ⊆ Set.range (chart a r))
    (hrq : Set.range (chart a r) ⊆ Set.range (chart a q))
    (hsq : Set.range (chart a s) ⊆ Set.range (chart a q)) :
    restriction a hd s q hsq =
      (restriction a hd s r hsr).comp (restriction a hd r q hrq) :=
  congrArg IndexedAffinoidAtlas.DirectedDomain.Inclusion.restriction
    (@Subsingleton.elim (IndexedAffinoidAtlas.DirectedDomain.Inclusion
      (s.directedDomain a hd) (q.directedDomain a hd))
      inferInstance (inclusion a hd s q hsq)
      (inclusion a hd s r hsr ≫ inclusion a hd r q hrq))

/-- The rational enlargement uses every original chart and has no greatest-chart
hypothesis. Its spectrum charts and bounded restrictions are constructed. -/
def atlas : IndexedAffinoidAtlas.{u, v, v} K X where
  Index := Index a
  algebra s := (s.rational a).algebra
  chart := chart a
  isEmbedding_chart := isEmbedding_chart a
  chartDomain_injective := chartDomain_injective a
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := by
    simpa only [family, range_chart] using isNet_family a
  restriction := restriction a hd
  restriction_chart := restriction_chart a hd
  restriction_universal := restriction_universal a hd
  restriction_id := restriction_id a hd
  restriction_comp := restriction_comp a hd

/-- Exactly the local rational loci occur, independently of chosen presentations. -/
theorem atlas_chartFamily :
    Set.range (fun s => Set.range ((atlas a hd).chart s)) = family a := by
  change Set.range (fun s : Index a => Set.range (chart a s)) = family a
  simp only [range_chart, family]

/-- Each original literal chart locus remains in the enlargement. -/
theorem atlas_ofOriginal_range (i : a.Index) :
    Set.range ((atlas a hd).chart (Index.ofOriginal a i)) = Set.range (a.chart i) :=
  (range_chart a _).trans (Index.val_ofOriginal a i)

/-- Every actual rational domain in every original chart occurs. -/
theorem atlas_ofChart_range (i : a.Index) (d : RationalChart K (a.algebra i)) :
    Set.range ((atlas a hd).chart (Index.ofChart a i d)) = locus a i d :=
  range_chart a _

/-- The enlarged atlas retains directedness: original upper charts still occur
as whole rational loci and contain all their local rational subdomains. -/
theorem atlas_hasDirectedCharts : (atlas a hd).HasDirectedCharts := by
  intro s r
  change Index a at s r
  obtain ⟨q, hsq, hrq⟩ := hd (s.original a) (r.original a)
  refine ⟨Index.ofOriginal a q, ?_, ?_⟩
  · rw [atlas_ofOriginal_range]
    change Set.range (chart a s) ⊆ Set.range (a.chart q)
    rw [range_chart, ← s.locus_original_rational a]
    rintro _ ⟨x, _, rfl⟩
    exact hsq ⟨x, rfl⟩
  · rw [atlas_ofOriginal_range]
    change Set.range (chart a r) ⊆ Set.range (a.chart q)
    rw [range_chart, ← r.locus_original_rational a]
    rintro _ ⟨x, _, rfl⟩
    exact hrq ⟨x, rfl⟩

end Langlands.Analytic.DirectedRationalAtlas
