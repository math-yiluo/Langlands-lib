import Langlands.Geometry.Analytic.CoherentQuasiIsoReversePullback
import Langlands.Geometry.Analytic.CofinalImageStrongInverses
import Langlands.Geometry.Analytic.CommonSubatlas
import Langlands.Geometry.Analytic.CompatibleStrongMaps
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections
import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph

/-! # Actual reverse strong maps on locally refining target subatlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

namespace AtlasTopology

variable {X : Type v} [TopologicalSpace X]

/-- Intersect an ambient finite neighborhood with each member of any family.
Only the second family needs a quasinet. -/
theorem IsQuasinet.locallyRefines_intersectionFamily {τ υ : Set (Set X)}
    (hυ : IsQuasinet υ) : LocallyRefines (intersectionFamily τ υ) τ := by
  intro U hU x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ := hυ x
  let δ : Set (Set X) := (fun V => U ∩ V) '' σ
  have heq : ⋃₀ δ = U ∩ ⋃₀ σ := by
    ext y
    constructor
    · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
      exact ⟨hy.1, V, hV, hy.2⟩
    · rintro ⟨hyU, V, hV, hyV⟩
      exact ⟨_, ⟨V, hV, rfl⟩, hyU, hyV⟩
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨U, hU, V, hs hV, rfl⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨inter_subset_left, hx, hm V hV⟩
  · rw [heq]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hn)

end AtlasTopology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Downward selection preserves actual full-domain closure: represent the
same local domain in the original atlas, then use its containment in its parent. -/
theorem subatlas_hasAllLocalDomains (ha : a.HasAllLocalDomains)
    (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)
    (hd : a.IsDownwardClosedSelection P) : (a.subatlas P hP).HasAllLocalDomains := by
  apply Set.Subset.antisymm ?_ (a.subatlas P hP).chartFamily_subset_localDomainFamily
  rintro _ ⟨U, rfl⟩
  let V : LocalDomain a := ⟨U.index.val, U.domain⟩
  obtain ⟨i, hi⟩ := ha.exists_chart V
  have hparent : Set.range (a.chart i) ⊆ Set.range (a.chart U.index.val) := by
    rw [hi]
    exact Set.image_subset_range _ _
  exact ⟨⟨i, hd i U.index.val hparent U.index.property⟩, hi⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom.IsQuasiIso

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A B} (hf : f.IsQuasiIso)

/-- Original target charts contained in one complete original source-chart image. -/
def reverseChartSelection (_hf : f.IsQuasiIso) (j : B.atlas.Index) : Prop :=
  ∃ i, Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)

theorem reverseChartSelection_downward :
    B.atlas.IsDownwardClosedSelection hf.reverseChartSelection := by
  intro j j' h
  rintro ⟨i, hi⟩
  exact ⟨i, h.trans hi⟩

/-- Image charts form an ambient quasinet by the actual homeomorphism. Target
closure realizes each image as an original chart; the target net then refines
its intersections with every original target chart by selected original charts. -/
theorem reverseChartSelection_locallyRefining (hb : B.atlas.HasAllLocalDomains) :
    B.atlas.IsLocallyRefiningSelection hf.reverseChartSelection := by
  let τ := Set.range (fun j => Set.range (B.atlas.chart j))
  let υ := AtlasTopology.imageFamily hf.1.homeomorph
    (Set.range (fun i => Set.range (A.atlas.chart i)))
  have hυ : AtlasTopology.IsQuasinet υ :=
    A.atlas.isNet_chartFamily.1.imageFamily hf.1.homeomorph
  apply hυ.locallyRefines_intersectionFamily.trans
  rintro _ ⟨U, hU, V, hV, rfl⟩ x hx
  obtain ⟨T, ⟨i, rfl⟩, rfl⟩ := hV
  have hVτ : f.baseMap '' Set.range (A.atlas.chart i) ∈ τ := by
    refine ⟨hf.imageOriginalChartIndex hb (A.atlas.originalLocalDomain i), ?_⟩
    exact (hf.range_imageOriginalChartIndex hb (A.atlas.originalLocalDomain i)).trans
      (congrArg (fun S : Set A.space => f.baseMap '' S)
        (A.atlas.originalLocalDomain_locus i))
  obtain ⟨σ, hfσ, hs, hm, hn⟩ :=
    B.atlas.isNet_chartFamily.locallyRefines_intersectionFamily
      _ ⟨U, hU, _, hVτ, rfl⟩ x hx
  refine ⟨σ, hfσ, ?_, hm, hn⟩
  intro W hW
  obtain ⟨j, hj⟩ := hs hW
  refine ⟨⟨j, i, ?_⟩, hj⟩
  change Set.range (B.atlas.chart j) = W at hj
  rw [hj]
  exact (hm W hW).1.trans Set.inter_subset_right

/-- A same-space original target subatlas whose charts have actual reverse maps. -/
def reverseSubpresentation (hb : B.atlas.HasAllLocalDomains) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  B.subpresentation hf.reverseChartSelection (hf.reverseChartSelection_locallyRefining hb)

theorem reverseSubpresentation_hasAllLocalDomains (hb : B.atlas.HasAllLocalDomains) :
    (hf.reverseSubpresentation hb).atlas.HasAllLocalDomains :=
  B.atlas.subatlas_hasAllLocalDomains hb hf.reverseChartSelection
    (hf.reverseChartSelection_locallyRefining hb) hf.reverseChartSelection_downward

/-- Every admissible reverse pullback is the constructed bounded restriction
between the original algebras. Coherence gives its two-variable restriction law. -/
def reverseStrongMap (hc : f.HasCoherentPullbacks) (hb : B.atlas.HasAllLocalDomains) :
    StrongHom (hf.reverseSubpresentation hb) A where
  baseMap := hf.inverseBaseMap
  target_exists j := by
    obtain ⟨i, hi⟩ := j.property
    exact ⟨i, (hf.inverse_admissible_iff j.val i).mpr hi⟩
  pullback j i h :=
    hf.reverseChartPullback j.val i ((hf.inverse_admissible_iff j.val i).mp h)
  chart_comm j i h x := by
    apply hf.1.injective
    exact (hf.reverseChartPullback_chart j.val i
      ((hf.inverse_admissible_iff j.val i).mp h) x).trans
        (hf.baseMap_inverseBaseMap (B.atlas.chart j.val x)).symm
  restriction_comm j j' i i' hj hi h h' :=
    hf.reverseChartPullback_naturality hc j.val j'.val i i' hj hi
      ((hf.inverse_admissible_iff j.val i).mp h)
      ((hf.inverse_admissible_iff j'.val i').mp h')

@[simp]
theorem reverseStrongMap_baseMap (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) :
    (hf.reverseStrongMap hc hb).baseMap = hf.inverseBaseMap := rfl

@[simp]
theorem reverseStrongMap_pullback (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) (j : (hf.reverseSubpresentation hb).atlas.Index)
    (i : A.atlas.Index)
    (h : hf.inverseBaseMap '' Set.range (B.atlas.chart j.val) ⊆
      Set.range (A.atlas.chart i)) :
    (hf.reverseStrongMap hc hb).pullback j i h =
      hf.reverseChartPullback j.val i ((hf.inverse_admissible_iff j.val i).mp h) := rfl

/-- Transport the complete inclusion representation along the exact image
locus equality. The ambient map is the inverse homeomorphism. -/
theorem reverseStrongMap_isQuasiIso (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) : (hf.reverseStrongMap hc hb).IsQuasiIso := by
  refine ⟨hf.1.homeomorph.symm.isHomeomorph, ?_⟩
  intro j i h
  have hrep := hf.reverseChartPullback_represents j.val i
    ((hf.inverse_admissible_iff j.val i).mp h)
  have hlocus :
      (fun x : BanachSpectrum (A.atlas.algebra i) => f.baseMap (A.atlas.chart i x)) ⁻¹'
          Set.range (B.atlas.chart j.val) =
        (hf.reverseStrongMap hc hb).chartImageLocus j i := by
    ext x
    change f.baseMap (A.atlas.chart i x) ∈ Set.range (B.atlas.chart j.val) ↔
      A.atlas.chart i x ∈ hf.inverseBaseMap '' Set.range (B.atlas.chart j.val)
    constructor
    · intro hx
      exact ⟨f.baseMap (A.atlas.chart i x), hx, hf.inverseBaseMap_baseMap _⟩
    · rintro ⟨y, hy, heq⟩
      have heq' := congrArg f.baseMap heq
      rw [hf.baseMap_inverseBaseMap] at heq'
      exact heq' ▸ hy
  exact hlocus ▸ hrep

/-- The constructed reverse source remains full-domain closed, which proves
intrinsic coefficient-test coherence of the reverse map. -/
theorem reverseStrongMap_hasCoherentPullbacks (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) : (hf.reverseStrongMap hc hb).HasCoherentPullbacks :=
  (hf.reverseStrongMap hc hb).hasCoherentPullbacks_of_saturated
    (hf.reverseSubpresentation_hasAllLocalDomains hb)

/-- An actual locally compatible reverse morphism, retaining every bounded map. -/
def reverseCompatibleStrongMap (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) :
    CompatibleStrongHom (hf.reverseSubpresentation hb) A :=
  CompatibleStrongHom.ofSaturated (hf.reverseStrongMap hc hb)
    (hf.reverseSubpresentation_hasAllLocalDomains hb)

@[simp]
theorem reverseCompatibleStrongMap_toStrongHom (hc : f.HasCoherentPullbacks)
    (hb : B.atlas.HasAllLocalDomains) :
    (hf.reverseCompatibleStrongMap hc hb).toStrongHom = hf.reverseStrongMap hc hb := rfl

end AffinoidAtlasPresentation.StrongHom.IsQuasiIso
end Langlands.Analytic
