import Langlands.Geometry.Analytic.ChosenAtlasCompactOpenSectionGluing
import Langlands.Geometry.Analytic.OriginalDomainCompactCover

/-! # Automatic finite local stabilization on compact domains of open-chart atlases -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic

open CategoryTheory Set Filter Topology
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {Y : Type v} [TopologicalSpace Y] (a : IndexedAffinoidAtlas.{u, v, w} K Y)

/-- Every original domain is open when the actual original chart ranges
are open. This follows from contained-chart point coverage. -/
theorem isOpen_originalChartDomain
    (hO : ∀ i, IsOpen (Set.range (a.chart i))) (S : a.OriginalChartDomain) :
    IsOpen (S : Set Y) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨σ, _, hσ, _, hn⟩ := S.is_domain ⟨x, hx⟩
  obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨_, ⟨i, rfl⟩, hiS, rfl⟩ := hσ hU
  exact mem_of_superset ((hO i).mem_nhds hxU) hiS

namespace OriginalChartDomain

variable {a} {S : a.OriginalChartDomain}

/-- Choose actual finitely many original chart members inside a covering
sieve whose subsets cover the compact target. No Hausdorff hypothesis. -/
def compactSieveChartPointCover (hS : IsCompact (S : Set Y))
    (R : Sieve S) (hR : IsCovering R) : Finset (SieveChart R) :=
  Classical.choose (hR.sieveChartFamily.exists_finset_cover hS)

theorem compactSieveChartPointCover_covers (hS : IsCompact (S : Set Y))
    (R : Sieve S) (hR : IsCovering R) :
    (⋃ c : compactSieveChartPointCover hS R hR, (c.val.domain : Set Y)) =
      (S : Set Y) := by
  have heq :
      (⋃ c : compactSieveChartPointCover hS R hR, (c.val.domain : Set Y)) =
        ⋃ c ∈ compactSieveChartPointCover hS R hR, (c.domain : Set Y) := by
    ext x
    simp
  exact heq.trans (Classical.choose_spec
    (hR.sieveChartFamily.exists_finset_cover hS))

end OriginalChartDomain
end IndexedAffinoidAtlas

namespace DisjointAffinoidAtlas

/-- In the constructed disjoint union of actual affinoid spectra, every
original-chart domain is open; the charts are already proved clopen. -/
theorem isOpen_originalChartDomain {I : Type v}
    (B : I → PresentedAffinoidAlgebra K) (S : (atlas B).OriginalChartDomain) :
    IsOpen (S : Set (Space B)) :=
  (atlas B).isOpen_originalChartDomain
    (fun c => (isClopen_chartDomain B c).isOpen) S

end DisjointAffinoidAtlas

namespace AffinoidAtlasPresentation.ChosenAtlasSectionAction

variable {G : Type t} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Action (AffinoidAtlasPresentation.{u, v, w} K) G)
  (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
  (hO : ∀ i, IsOpen (Set.range (X.V.atlas.chart i)))
  {D : Type z} {S : X.V.atlas.OriginalChartDomain}
  (hS : IsCompact (S : Set X.V.space))
  {R : Sieve S}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf X.V.atlas D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- The actual glue on an arbitrary compact original domain is a
compact-open pair, with openness derived from the original open charts. -/
def openChartSieveGlue : CompactOpenOriginalDomainSection X.V D :=
  ⟨OriginalDomainSection.sieveGlue p hp hR,
    hS, X.V.atlas.isOpen_originalChartDomain hO S⟩

/-- Extract the finite local charts from compactness and the entire
covering sieve, then construct their common full open stabilizer inside U. -/
def openChartGlueOpenStabilizer (U : OpenSubgroup G) : OpenSubgroup G :=
  finiteSieveGlueOpenStabilizer X hX p
    (fun c : compactSieveChartPointCover hS R hR => c.val.domain)
    (fun c => c.val.inclusion) (fun c => c.val.mem)
    (fun c => isCompact_range (X.V.atlas.isEmbedding_chart c.val.val.val).continuous)
    (fun c => hO c.val.val.val) U

theorem openChartGlueOpenStabilizer_le (U : OpenSubgroup G) :
    openChartGlueOpenStabilizer X hX hO hS p hR U ≤ U :=
  finiteSectionOpenStabilizer_le X hX U _

/-- No selected finite subcover or global fixedness is supplied: compactness
extracts actual local chart members and their common subgroup fixes the glue. -/
theorem openChartSieveGlue_fixed (U : OpenSubgroup G) (g : G)
    (hg : g ∈ openChartGlueOpenStabilizer X hX hO hS p hR U) :
    g • openChartSieveGlue X hO hS p hp hR =
      openChartSieveGlue X hO hS p hp hR := by
  exact finiteSieveGlue_fixed X hX p hp hR
    (fun c : compactSieveChartPointCover hS R hR => c.val.domain)
    (fun c => c.val.inclusion) (fun c => c.val.mem)
    (fun c => isCompact_range (X.V.atlas.isEmbedding_chart c.val.val.val).continuous)
    (fun c => hO c.val.val.val)
    (compactSieveChartPointCover_covers hS R hR) U g hg

/-- The constructed open local subgroup is contained in the entire actual
compact original-domain glue stabilizer. -/
theorem openChartGlueOpenStabilizer_le_glue (U : OpenSubgroup G) :
    (openChartGlueOpenStabilizer X hX hO hS p hR U).toSubgroup ≤
      MulAction.stabilizer G (openChartSieveGlue X hO hS p hp hR) := by
  intro g hg
  exact openChartSieveGlue_fixed X hX hO hS p hp hR U g hg

end AffinoidAtlasPresentation.ChosenAtlasSectionAction

end Langlands.Analytic
