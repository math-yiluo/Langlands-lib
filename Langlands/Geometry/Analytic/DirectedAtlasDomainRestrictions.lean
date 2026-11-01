import Langlands.Geometry.Analytic.AtlasAffinoidDomainExtension
import Langlands.Geometry.Analytic.DirectedAtlasMaps

/-! # Bounded restrictions between full domains in directed original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- An ambient containment becomes a full-domain containment in any common
original upper chart. -/
theorem extendDomain_locus_subset_of_chart_image_subset
    (i j q : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    (a.extendDomain i q hiq U).locus ⊆ (a.extendDomain j q hjq V).locus := by
  intro x hx
  have hx' : a.chart q x ∈ a.chart j '' V.locus := by
    apply h
    rw [← a.chart_image_extendDomain_locus i q hiq U]
    exact ⟨x, hx, rfl⟩
  rw [← a.chart_image_extendDomain_locus j q hjq V] at hx'
  obtain ⟨y, hy, he⟩ := hx'
  exact (a.isEmbedding_chart q).injective he ▸ hy

/-- The bounded restriction is constructed by full factorization over the
chosen upper chart; the represented algebras are unchanged by extension. -/
def domainRestrictionToUpper
    (i j q : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    BoundedAlgHom K V.algebra U.algebra :=
  (Domain.inclusionOfSubset (a.extendDomain i q hiq U) (a.extendDomain j q hjq V)
    (a.extendDomain_locus_subset_of_chart_image_subset i j q U V hiq hjq h)).restriction

theorem domainRestrictionToUpper_comp_baseMap
    (i j q : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    (a.domainRestrictionToUpper i j q U V hiq hjq h).comp
        (V.baseMap.comp (a.restriction j q hjq)) =
      U.baseMap.comp (a.restriction i q hiq) :=
  (Domain.inclusionOfSubset (a.extendDomain i q hiq U) (a.extendDomain j q hjq V)
    (a.extendDomain_locus_subset_of_chart_image_subset i j q U V hiq hjq h)).comp_baseMap

/-- The unchanged represented algebra has the same structural map after
passing through another original containing chart. -/
theorem extendDomain_baseMap_comp_restriction
    (i q r : a.Index) (U : Domain K (a.algebra i))
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hqr : Set.range (a.chart q) ⊆ Set.range (a.chart r))
    (hir : Set.range (a.chart i) ⊆ Set.range (a.chart r)) :
    (U.baseMap.comp (a.restriction i q hiq)).comp (a.restriction q r hqr) =
      U.baseMap.comp (a.restriction i r hir) := by
  rw [BoundedAlgHom.comp_assoc, ← a.restriction_comp i q r hiq hqr hir]

/-- Directedness proves existence of one bounded map over every common upper
chart and uniqueness of that entire map, with no greatest chart supplied. -/
theorem directedDomainRestriction_existsUnique (hd : a.HasDirectedCharts)
    (i j : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    ∃! f : BoundedAlgHom K V.algebra U.algebra,
      ∀ (q : a.Index)
        (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
        (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q)),
        f.comp (V.baseMap.comp (a.restriction j q hjq)) =
          U.baseMap.comp (a.restriction i q hiq) := by
  obtain ⟨q₀, hi₀, hj₀⟩ := hd i j
  let f := a.domainRestrictionToUpper i j q₀ U V hi₀ hj₀ h
  have hf := a.domainRestrictionToUpper_comp_baseMap i j q₀ U V hi₀ hj₀ h
  refine ⟨f, ?_, ?_⟩
  · intro q hiq hjq
    obtain ⟨r, h₀r, hqr⟩ := hd q₀ q
    apply a.restriction_hom_ext q r hqr U.algebra
    calc
      (f.comp (V.baseMap.comp (a.restriction j q hjq))).comp
          (a.restriction q r hqr) =
          f.comp (V.baseMap.comp (a.restriction j r (hjq.trans hqr))) := by
        rw [BoundedAlgHom.comp_assoc, a.extendDomain_baseMap_comp_restriction]
      _ = (f.comp (V.baseMap.comp (a.restriction j q₀ hj₀))).comp
          (a.restriction q₀ r h₀r) := by
        rw [BoundedAlgHom.comp_assoc, a.extendDomain_baseMap_comp_restriction]
      _ = (U.baseMap.comp (a.restriction i q₀ hi₀)).comp
          (a.restriction q₀ r h₀r) := by rw [hf]
      _ = U.baseMap.comp (a.restriction i r (hiq.trans hqr)) :=
        a.extendDomain_baseMap_comp_restriction i q₀ r U hi₀ h₀r (hiq.trans hqr)
      _ = (U.baseMap.comp (a.restriction i q hiq)).comp
          (a.restriction q r hqr) :=
        (a.extendDomain_baseMap_comp_restriction i q r U hiq hqr (hiq.trans hqr)).symm
  · intro g hg
    exact Domain.boundedHom_eq_of_over_base
      (a.extendDomain j q₀ hj₀ V) (a.extendDomain i q₀ hi₀ U) g f
      (hg q₀ hi₀ hj₀) hf

/-- The unique actual bounded restriction between locally represented domains
whose ambient subsets are contained. -/
def directedDomainRestriction (hd : a.HasDirectedCharts)
    (i j : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    BoundedAlgHom K V.algebra U.algebra :=
  Classical.choose (a.directedDomainRestriction_existsUnique hd i j U V h).exists

theorem directedDomainRestriction_comp_baseMap (hd : a.HasDirectedCharts)
    (i j : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (q : a.Index)
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q)) :
    (a.directedDomainRestriction hd i j U V h).comp
        (V.baseMap.comp (a.restriction j q hjq)) =
      U.baseMap.comp (a.restriction i q hiq) :=
  Classical.choose_spec (a.directedDomainRestriction_existsUnique hd i j U V h).exists
    q hiq hjq

/-- One actual equation over a common original upper chart determines every
bounded restriction between the two represented algebras. -/
theorem eq_directedDomainRestriction_of_over_base (hd : a.HasDirectedCharts)
    (i j : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (q : a.Index)
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q))
    (f : BoundedAlgHom K V.algebra U.algebra)
    (hf : f.comp (V.baseMap.comp (a.restriction j q hjq)) =
      U.baseMap.comp (a.restriction i q hiq)) :
    f = a.directedDomainRestriction hd i j U V h :=
  Domain.boundedHom_eq_of_over_base
    (a.extendDomain j q hjq V) (a.extendDomain i q hiq U) f _
    hf (a.directedDomainRestriction_comp_baseMap hd i j U V h q hiq hjq)

/-- Every choice of common upper produces exactly the same bounded map. -/
theorem domainRestrictionToUpper_eq_directedDomainRestriction (hd : a.HasDirectedCharts)
    (i j q : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (hiq : Set.range (a.chart i) ⊆ Set.range (a.chart q))
    (hjq : Set.range (a.chart j) ⊆ Set.range (a.chart q))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    a.domainRestrictionToUpper i j q U V hiq hjq h =
      a.directedDomainRestriction hd i j U V h :=
  a.eq_directedDomainRestriction_of_over_base hd i j U V h q hiq hjq _
    (a.domainRestrictionToUpper_comp_baseMap i j q U V hiq hjq h)

/-- The constructed bounded map respects the actual ambient chart maps. -/
theorem directedDomainRestriction_chart (hd : a.HasDirectedCharts)
    (i j : a.Index) (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (x : BanachSpectrum U.algebra) :
    a.chart j (V.spectrumMap
        (BanachSpectrum.comap (a.directedDomainRestriction hd i j U V h).toBoundedRingHom x)) =
      a.chart i (U.spectrumMap x) := by
  obtain ⟨q, hiq, hjq⟩ := hd i j
  calc
    a.chart j (V.spectrumMap
        (BanachSpectrum.comap (a.directedDomainRestriction hd i j U V h).toBoundedRingHom x)) =
        a.chart q (BanachSpectrum.comap (a.restriction j q hjq).toBoundedRingHom
          (V.spectrumMap (BanachSpectrum.comap
            (a.directedDomainRestriction hd i j U V h).toBoundedRingHom x))) :=
      (a.restriction_chart j q hjq _).symm
    _ = a.chart q (BanachSpectrum.comap (a.restriction i q hiq).toBoundedRingHom
        (U.spectrumMap x)) := by
      congr 1
      apply BanachSpectrum.ext
      intro b
      exact congrArg (fun f : BoundedAlgHom K (a.algebra q) U.algebra => x (f b))
        (a.directedDomainRestriction_comp_baseMap hd i j U V h q hiq hjq)
    _ = a.chart i (U.spectrumMap x) := a.restriction_chart i q hiq _

/-- In one original chart, the construction recovers every existing actual
full-domain inclusion, including its entire bounded restriction. -/
theorem directedDomainRestriction_sameChart (hd : a.HasDirectedCharts)
    (i : a.Index) {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    a.directedDomainRestriction hd i i U V (Set.image_mono f.subset) =
      f.restriction := by
  symm
  apply a.eq_directedDomainRestriction_of_over_base hd i i U V
    (Set.image_mono f.subset) i Subset.rfl Subset.rfl
  simpa only [a.restriction_id, BoundedAlgHom.comp_id] using f.comp_baseMap

@[simp]
theorem directedDomainRestriction_id (hd : a.HasDirectedCharts)
    (i : a.Index) (U : Domain K (a.algebra i)) :
    a.directedDomainRestriction hd i i U U Subset.rfl =
      BoundedAlgHom.id K U.algebra :=
  a.directedDomainRestriction_sameChart hd i (𝟙 U)

/-- Bounded restrictions compose across three independently chosen original
charts. Full uniqueness over a common upper proves equality of algebra maps. -/
theorem directedDomainRestriction_comp (hd : a.HasDirectedCharts)
    (i j k : a.Index) (U : Domain K (a.algebra i))
    (V : Domain K (a.algebra j)) (W : Domain K (a.algebra k))
    (hUV : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (hVW : a.chart j '' V.locus ⊆ a.chart k '' W.locus)
    (hUW : a.chart i '' U.locus ⊆ a.chart k '' W.locus) :
    (a.directedDomainRestriction hd i j U V hUV).comp
        (a.directedDomainRestriction hd j k V W hVW) =
      a.directedDomainRestriction hd i k U W hUW := by
  obtain ⟨r, hir, hjr⟩ := hd i j
  obtain ⟨q, hrq, hkq⟩ := hd r k
  have hiq := hir.trans hrq
  have hjq := hjr.trans hrq
  apply a.eq_directedDomainRestriction_of_over_base hd i k U W hUW q hiq hkq
  rw [BoundedAlgHom.comp_assoc,
    a.directedDomainRestriction_comp_baseMap hd j k V W hVW q hjq hkq,
    a.directedDomainRestriction_comp_baseMap hd i j U V hUV q hiq hjq]

end Langlands.Analytic.IndexedAffinoidAtlas
