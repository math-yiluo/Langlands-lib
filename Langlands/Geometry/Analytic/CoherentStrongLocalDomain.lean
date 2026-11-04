import Langlands.Geometry.Analytic.CoherentStrongDomainPullback

/-! # Constructed strong pullbacks between arbitrary local full domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The target domain's original parent contains the entire local image. -/
theorem localDomain_parent_admissible (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index) :=
  h.trans (B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl)

/-- The constructed parent-chart map lands in the full target domain. -/
theorem localChartPullback_image_domain (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    HasImageIn K (f.localChartPullback U V.index
      (f.localDomain_parent_admissible U V h)) V.domain.locus := by
  intro x
  obtain ⟨y, hy, heq⟩ := h ⟨U.ambientMap x,
    ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩
  have hxy := (B.atlas.isEmbedding_chart V.index).injective
    ((f.localChartPullback_chart U V.index
      (f.localDomain_parent_admissible U V h) x).trans heq.symm)
  exact hxy.symm ▸ hy

/-- Factor the actual parent-chart pullback through the unchanged target
full-domain algebra, using its universal property on the source algebra. -/
def localDomainPullback (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    BoundedAlgHom K V.algebra U.algebra :=
  (V.domain.represents.2.2 U.algebra
    (f.localChartPullback U V.index (f.localDomain_parent_admissible U V h))
    (f.localChartPullback_image_domain U V h)).choose

/-- The factorization preserves the complete bounded structural map. -/
theorem localDomainPullback_comp_baseMap (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    (f.localDomainPullback U V h).comp V.domain.baseMap =
      f.localChartPullback U V.index (f.localDomain_parent_admissible U V h) :=
  (V.domain.represents.2.2 U.algebra
    (f.localChartPullback U V.index (f.localDomain_parent_admissible U V h))
    (f.localChartPullback_image_domain U V h)).choose_spec.1

/-- Full-domain uniqueness, rather than equality on spectrum points,
determines each factored bounded map. -/
theorem localDomainPullback_unique (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (hφ : φ.comp V.domain.baseMap =
      f.localChartPullback U V.index (f.localDomain_parent_admissible U V h)) :
    φ = f.localDomainPullback U V h :=
  V.domain.represents.hom_ext U.algebra φ _
    (hφ.trans (f.localDomainPullback_comp_baseMap U V h).symm)

/-- The factorized spectrum map has the original ambient map. -/
theorem localDomainPullback_ambient (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) (x : BanachSpectrum U.algebra) :
    V.ambientMap (BanachSpectrum.comap (f.localDomainPullback U V h).toBoundedRingHom x) =
      f.baseMap (U.ambientMap x) := by
  have heq : V.domain.spectrumMap
      (BanachSpectrum.comap (f.localDomainPullback U V h).toBoundedRingHom x) =
      BanachSpectrum.comap (f.localChartPullback U V.index
        (f.localDomain_parent_admissible U V h)).toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (B.atlas.algebra V.index) U.algebra =>
      x (q b)) (f.localDomainPullback_comp_baseMap U V h)
  exact (congrArg (B.atlas.chart V.index) heq).trans
    (f.localChartPullback_chart U V.index (f.localDomain_parent_admissible U V h) x)

/-- Every containing original target chart retains its complete structural
map after the target-domain factorization. -/
theorem localDomainPullback_comp_chart (f : StrongHom A B)
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) (j : B.atlas.Index)
    (hV : V.locus ⊆ Set.range (B.atlas.chart j))
    (hU : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    (f.localDomainPullback U V h).comp
        (B.atlas.domainChartRestriction V.index j V.domain hV) =
      f.localChartPullback U j hU := by
  have hc := (B.atlas.domainChartRestriction_isMapChartChange V.index j V.domain hV).comp
    B.atlas (f.localDomainPullback U V h)
  rw [f.localDomainPullback_comp_baseMap U V h] at hc
  have himage (x : BanachSpectrum U.algebra) :
      B.atlas.chart V.index (BanachSpectrum.comap
        (f.localChartPullback U V.index
          (f.localDomain_parent_admissible U V h)).toBoundedRingHom x) ∈
        Set.range (B.atlas.chart j) := by
    rw [f.localChartPullback_chart]
    exact hU ⟨U.ambientMap x,
      ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩
  exact (B.atlas.eq_changeMapChart V.index j U.algebra _ himage _ hc).trans
    (f.localChartPullback_change U V.index j
      (f.localDomain_parent_admissible U V h) hU himage)

/-- Source inclusions commute with the complete factored maps under the
intrinsic law on the original supplied pullbacks. -/
theorem localDomainPullback_source (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    {U U' : LocalDomain A.atlas} (p : U ⟶ U') (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) (h' : f.baseMap '' U'.locus ⊆ V.locus) :
    p.restriction.comp (f.localDomainPullback U' V h') = f.localDomainPullback U V h := by
  apply V.domain.represents.hom_ext U.algebra
  rw [BoundedAlgHom.comp_assoc, f.localDomainPullback_comp_baseMap,
    f.localChartPullback_source hf, f.localDomainPullback_comp_baseMap]

/-- Target inclusions commute with the complete factored maps, without a
coherence hypothesis on the original strong map. -/
theorem localDomainPullback_target (f : StrongHom A B) (U : LocalDomain A.atlas)
    {V W : LocalDomain B.atlas} (q : V ⟶ W)
    (hV : f.baseMap '' U.locus ⊆ V.locus) (hW : f.baseMap '' U.locus ⊆ W.locus) :
    (f.localDomainPullback U V hV).comp q.restriction = f.localDomainPullback U W hW := by
  have hq : q.restriction.comp W.domain.baseMap =
      B.atlas.domainChartRestriction V.index W.index V.domain
        (B.atlas.domainSubset_chart V.index W.index V.domain W.domain q.subset) := by
    simpa only [B.atlas.domainChartRestriction_self] using
      q.comp_chart W.index
        (B.atlas.domainSubset_chart V.index W.index V.domain W.domain q.subset)
        (B.atlas.domainSubset_chart W.index W.index W.domain W.domain Subset.rfl)
  apply W.domain.represents.hom_ext U.algebra
  rw [BoundedAlgHom.comp_assoc, hq, f.localDomainPullback_comp_baseMap]
  exact f.localDomainPullback_comp_chart U V hV W.index
    (B.atlas.domainSubset_chart V.index W.index V.domain W.domain q.subset)
    (f.localDomain_parent_admissible U W hW)

/-- The full two-variable restriction equation for arbitrary source and target
local-domain inclusions. -/
theorem localDomainPullback_naturality (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (p : U ⟶ U') (q : V ⟶ V')
    (h : f.baseMap '' U.locus ⊆ V.locus) (h' : f.baseMap '' U'.locus ⊆ V'.locus) :
    p.restriction.comp (f.localDomainPullback U' V' h') =
      (f.localDomainPullback U V h).comp q.restriction := by
  have hUV' := (Set.image_mono p.subset).trans h'
  exact (f.localDomainPullback_source hf p V' hUV' h').trans
    (f.localDomainPullback_target U q h hUV').symm

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
