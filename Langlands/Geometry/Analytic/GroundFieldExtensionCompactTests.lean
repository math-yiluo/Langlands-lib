import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionDomainSections
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlasAction
import Langlands.Geometry.Analytic.LocalizedChartTransport

/-! # Compact analytic domain tests for the coefficient action -/

noncomputable section

universe u u' v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Filter SaturatedAtlasPresentation PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open scoped Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "B" => atlas K L a
local notation "S" => ofSaturation (presentation K L a)

/-- Compactness gives a finite cover by full represented domains in the
scalar-extended charts. Their algebras are the stored saturated chart algebras. -/
def compactDomainChartCover (D : (S).AnalyticDomain) (hD : IsCompact D.carrier) :
    {s : Finset (S).presentation.atlas.Index //
      D.carrier = ⋃ i ∈ s, range ((S).presentation.atlas.chart i)} := by
  classical
  apply Classical.choice
  obtain ⟨σ, hfin, hcharts, hcov⟩ := (S).exists_finite_charts_of_isCompact D hD
  choose i hi hsub using fun V : σ => hcharts V.val V.property
  let := hfin.fintype
  refine ⟨⟨Finset.univ.image i, ?_⟩⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := mem_sUnion.mp (hcov hx)
    let T : σ := ⟨V, hV⟩
    exact mem_iUnion₂.mpr ⟨i T, Finset.mem_image_of_mem i (Finset.mem_univ T),
      (hi T).symm ▸ hxV⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hj
    exact hsub V ((hi V) ▸ hxj)

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* ↥(isometricAutomorphisms K L))
  (hρ : ∀ t : L, Continuous (fun g : G => (ρ g).val t))

private abbrev representative (i : (S).presentation.atlas.Index) :=
  (B).saturatedRepresentative i

private def chartSubgroup (i : (S).presentation.atlas.Index) : OpenSubgroup G :=
  domainCoverSectionOpenSubgroup K L (a.algebra (representative K L a i).index)
    (Domain.finiteRationalCoverData (representative K L a i).domain) ρ hρ

/-- A common open subgroup for the bounded section operators of a finite
family of charts of the scalar extension. -/
def chartFamilySectionSubgroup (s : Finset (S).presentation.atlas.Index) : OpenSubgroup G :=
  OpenSubgroup.iInfOfFinite (fun i : ↥s => chartSubgroup K L a ρ hρ i.val)

variable (s : Finset (atlas K L a).saturatedAtlas.Index)

private def chartElement (i : ↥s) (g : ↥(chartFamilySectionSubgroup K L a ρ hρ s)) : ↥(chartSubgroup K L a ρ hρ i.val) := by
  let H (j : ↥s) := chartSubgroup K L a ρ hρ j.val
  have hg : g.val ∈ OpenSubgroup.iInfOfFinite H := g.property
  exact ⟨g.val, OpenSubgroup.iInfOfFinite_le H i hg⟩

/-- The bounded semilinear operator on a full affinoid chart in the family,
with its original stored algebra. -/
def chartFamilySectionMap (i : ↥s) (g : ↥(chartFamilySectionSubgroup K L a ρ hρ s)) :
    BoundedRingHom ((S).presentation.atlas.algebra i.val)
      ((S).presentation.atlas.algebra i.val) :=
  openDomainSectionMap K L (a.algebra (representative K L a i.val).index)
    (Domain.finiteRationalCoverData (representative K L a i.val).domain) ρ hρ
    (chartElement K L a ρ hρ s i g)

/-- The action on each full-domain spectrum is the restriction of the glued
point action. -/
theorem chartFamilySectionMap_chart (i : ↥s) (g : ↥(chartFamilySectionSubgroup K L a ρ hρ s))
    (x : BanachSpectrum ((S).presentation.atlas.algebra i.val)) :
    (S).presentation.atlas.chart i.val
      (BanachSpectrum.comap (chartFamilySectionMap K L a ρ hρ s i g⁻¹) x) =
    coefficientPointMap K L a (ρ g) ((S).presentation.atlas.chart i.val x) := by
  let U := representative K L a i.val
  change (chartSystem K L a).chart U.index
    (BanachSpectrum.comap U.domain.baseMap.toBoundedRingHom
      (BanachSpectrum.comap (chartFamilySectionMap K L a ρ hρ s i g⁻¹) x)) =
    coefficientPointMap K L a (ρ g) ((chartSystem K L a).chart U.index
      (BanachSpectrum.comap U.domain.baseMap.toBoundedRingHom x))
  have hchart := coefficientPointMap_chart K L a (ρ g) U.index
    (BanachSpectrum.comap U.domain.baseMap.toBoundedRingHom x)
  refine Eq.trans ?_ hchart.symm
  apply congrArg ((chartSystem K L a).chart U.index)
  have h := comap_openDomainSectionMap K L (a.algebra U.index)
    (Domain.finiteRationalCoverData U.domain) ρ hρ (chartElement K L a ρ hρ s i g⁻¹) x
  change _ = BanachSpectrum.comap (coefficientHom K L (a.algebra U.index) (ρ (g.val⁻¹))).toBoundedRingHom
    (BanachSpectrum.comap U.domain.baseMap.toBoundedRingHom x) at h
  rw [map_inv] at h
  exact h

/-- Every element of the common open subgroup preserves the union of the
chart ranges. -/
theorem chartFamilySectionSubgroup_preimage (g : ↥(chartFamilySectionSubgroup K L a ρ hρ s)) :
    coefficientPointMap K L a (ρ g) ⁻¹' (⋃ i ∈ s, range ((S).presentation.atlas.chart i)) =
      ⋃ i ∈ s, range ((S).presentation.atlas.chart i) := by
  let U := ⋃ i ∈ s, range ((S).presentation.atlas.chart i)
  have hmaps (k : ↥(chartFamilySectionSubgroup K L a ρ hρ s)) : MapsTo (coefficientPointMap K L a (ρ k)) U U := by
    intro x hx
    obtain ⟨i, hi, y, rfl⟩ := mem_iUnion₂.mp hx
    let j : ↥s := ⟨i, hi⟩
    exact mem_iUnion₂.mpr ⟨i, hi, _, chartFamilySectionMap_chart K L a ρ hρ s j k y⟩
  ext x
  constructor
  · intro hx
    have hb := hmaps g⁻¹ hx
    let := coefficientMulAction K L a ρ
    change g.val⁻¹ • (g.val • x) ∈ U at hb
    rwa [inv_smul_smul] at hb
  · intro hx
    exact hmaps g hx

/-- The open subgroup attached to a compact domain fixes that domain. -/
theorem compactDomainChartCover_preimage (D : (S).AnalyticDomain) (hD : IsCompact D.carrier)
    (g : ↥(chartFamilySectionSubgroup K L a ρ hρ (compactDomainChartCover K L a D hD).val)) :
    coefficientPointMap K L a (ρ g) ⁻¹' D.carrier = D.carrier := by
  let charts := compactDomainChartCover K L a D hD
  let U : Set (chartSystem K L a).Space := D.carrier
  let V : Set (chartSystem K L a).Space := ⋃ i ∈ charts.val, range ((S).presentation.atlas.chart i)
  let f := coefficientPointMap K L a (ρ g)
  have hUV : U = V := charts.property
  have hV : f ⁻¹' V = V := chartFamilySectionSubgroup_preimage K L a ρ hρ charts.val g
  calc
    f ⁻¹' U = f ⁻¹' V := congrArg (f ⁻¹' ·) hUV
    _ = V := hV
    _ = U := hUV.symm

/-- The coordinate of any section on a full chart has a norm-continuous
orbit under the common open subgroup. -/
theorem continuous_chartFamilySectionMap (i : ↥s) (f : (S).presentation.atlas.algebra i.val) :
    Continuous (fun g : ↥(chartFamilySectionSubgroup K L a ρ hρ s) => chartFamilySectionMap K L a ρ hρ s i g f) := by
  let U := representative K L a i.val
  have hc : Continuous (chartElement K L a ρ hρ s i) := continuous_subtype_val.subtype_mk _
  exact (continuous_openDomainSectionMap K L (a.algebra U.index)
    (Domain.finiteRationalCoverData U.domain) ρ hρ f).comp hc

/-- One identity neighbourhood gives a uniform spectral bound on each
member of the finite chart cover, for any family of sections on its members. -/
theorem eventually_chartFamily_spectralDisplacement_le
    (f : ∀ i : ↥s, (S).presentation.atlas.algebra i.val)
    (ε : ↥s → ℝ) (hε : ∀ i, 0 < ε i) :
    ∀ᶠ g in 𝓝 (1 : ↥(chartFamilySectionSubgroup K L a ρ hρ s)), ∀ (i : ↥s) (x : BanachSpectrum ((S).presentation.atlas.algebra i.val)),
      x (chartFamilySectionMap K L a ρ hρ s i g (f i) - f i) ≤ ε i := by
  apply Filter.eventually_all.mpr
  intro i
  let U := representative K L a i.val
  have hc : Continuous (chartElement K L a ρ hρ s i) := continuous_subtype_val.subtype_mk _
  have h1 : chartElement K L a ρ hρ s i 1 = 1 := Subtype.ext rfl
  have ht := (hc.continuousAt (x := (1 : ↥(chartFamilySectionSubgroup K L a ρ hρ s)))).tendsto
  rw [h1] at ht
  exact ht.eventually (eventually_spectral_displacement_le K L (a.algebra U.index)
    (Domain.finiteRationalCoverData U.domain) ρ hρ (f i) (hε i))

/-- The spectral bounds on a finite chart family hold in a neighbourhood
of the identity of the original group. -/
theorem eventually_chartFamily_spectralDisplacement_le_ambient
    (f : ∀ i : ↥s, (S).presentation.atlas.algebra i.val)
    (ε : ↥s → ℝ) (hε : ∀ i, 0 < ε i) :
    ∀ᶠ g in 𝓝 (1 : G), ∃ hg : g ∈ chartFamilySectionSubgroup K L a ρ hρ s,
      ∀ (i : ↥s) (x : BanachSpectrum ((S).presentation.atlas.algebra i.val)),
        x (chartFamilySectionMap K L a ρ hρ s i ⟨g, hg⟩ (f i) - f i) ≤ ε i := by
  let H := chartFamilySectionSubgroup K L a ρ hρ s
  have hmap : Filter.map (fun g : H => (g : G)) (𝓝 (1 : H)) = 𝓝 (1 : G) :=
    H.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (1 : H)
  rw [← hmap]
  exact (eventually_chartFamily_spectralDisplacement_le K L a ρ hρ s f ε hε).mono
    fun g hg => ⟨g.property, hg⟩

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
