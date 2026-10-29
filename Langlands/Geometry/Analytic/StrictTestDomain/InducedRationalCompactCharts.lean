import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCharts
import Langlands.Geometry.Analytic.Spectrum.Properties
import Langlands.Topology.GroupAction.InducedCompactCharts

/-! # Compact chart nets of actual induced rational spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable (X : ρ.OpenSubgroupTransport)

instance : CompactSpace X.LocalSpectrum :=
  inferInstanceAs (CompactSpace (BanachSpectrum X.domain.obj.algebra))

instance : T2Space X.LocalSpectrum :=
  inferInstanceAs (T2Space (BanachSpectrum X.domain.obj.algebra))

instance : T2Space X.InducedSpectrum :=
  TopologicalInduction.t2Space_induced X.subgroup.toSubgroup X.subgroup.isOpen'

instance : LocallyCompactSpace X.InducedSpectrum :=
  TopologicalInduction.locallyCompactSpace_induced X.subgroup.toSubgroup X.subgroup.isOpen'

/-- The actual coset-component fibers of the induced rational quotient spectrum. -/
def inducedChartFamily : Set (Set X.InducedSpectrum) :=
  TopologicalInduction.cosetChartFamily X.subgroup.toSubgroup

theorem inducedComponent_fiber_mem_inducedChartFamily (c : G ⧸ X.subgroup.toSubgroup) :
    X.inducedComponent ⁻¹' {c} ∈ X.inducedChartFamily :=
  TopologicalInduction.fiber_mem_cosetChartFamily X.subgroup.toSubgroup c

theorem inducedChartDomain_mem_inducedChartFamily (a : G) :
    (X.inducedChartDomain a : Set X.InducedSpectrum) ∈ X.inducedChartFamily :=
  TopologicalInduction.range_chart_mem_cosetChartFamily X.subgroup.toSubgroup a

theorem isNet_inducedChartFamily : AtlasTopology.IsNet X.inducedChartFamily :=
  TopologicalInduction.isNet_cosetChartFamily X.subgroup.toSubgroup X.subgroup.isOpen'

theorem isCompactFamily_inducedChartFamily :
    AtlasTopology.IsCompactFamily X.inducedChartFamily :=
  TopologicalInduction.isCompactFamily_cosetChartFamily
    X.subgroup.toSubgroup X.subgroup.isOpen'

theorem isCompact_inducedComponent_fiber (c : G ⧸ X.subgroup.toSubgroup) :
    IsCompact (X.inducedComponent ⁻¹' {c}) :=
  (X.isCompactFamily_inducedChartFamily _
    (X.inducedComponent_fiber_mem_inducedChartFamily c)).1

theorem isCompact_inducedChartDomain (a : G) :
    IsCompact (X.inducedChartDomain a : Set X.InducedSpectrum) :=
  (X.isCompactFamily_inducedChartFamily _
    (X.inducedChartDomain_mem_inducedChartFamily a)).1

instance (a : G) : CompactSpace (X.inducedChartDomain a) :=
  isCompact_iff_compactSpace.mp (X.isCompact_inducedChartDomain a)

theorem finite_inducedComponent_image_of_isCompact {s : Set X.InducedSpectrum}
    (hs : IsCompact s) : (X.inducedComponent '' s).Finite :=
  TopologicalInduction.finite_component_image_of_isCompact
    X.subgroup.toSubgroup X.subgroup.isOpen' hs

theorem exists_finite_inducedChart_cover_of_isCompact {s : Set X.InducedSpectrum}
    (hs : IsCompact s) :
    ∃ C : Finset (G ⧸ X.subgroup.toSubgroup),
      s ⊆ ⋃ c ∈ C, (X.inducedChartDomain c.out : Set X.InducedSpectrum) :=
  TopologicalInduction.exists_finite_chart_cover_of_isCompact
    X.subgroup.toSubgroup X.subgroup.isOpen' hs

/-- Closed subsets with finitely many coset labels lie in a finite union of
the actual compact rational charts. -/
theorem isCompact_iff_isClosed_finite_inducedComponent_image
    {s : Set X.InducedSpectrum} :
    IsCompact s ↔ IsClosed s ∧ (X.inducedComponent '' s).Finite := by
  constructor
  · intro hs
    exact ⟨hs.isClosed, X.finite_inducedComponent_image_of_isCompact hs⟩
  · rintro ⟨hclosed, hfinite⟩
    have hc : IsCompact (⋃ c ∈ X.inducedComponent '' s, X.inducedComponent ⁻¹' {c}) :=
      hfinite.isCompact_biUnion fun c _ => X.isCompact_inducedComponent_fiber c
    apply hc.of_isClosed_subset hclosed
    intro z hz
    exact Set.mem_iUnion.mpr ⟨X.inducedComponent z,
      Set.mem_iUnion.mpr ⟨⟨z, hz, rfl⟩, rfl⟩⟩

namespace Hom

variable {X Y : ρ.OpenSubgroupTransport}

/-- Transport of coset labels agrees exactly with the component triangle. -/
theorem inducedComponent_image_inducedMap (f : X ⟶ Y) (s : Set X.InducedSpectrum) :
    Y.inducedComponent '' (f.inducedMap '' s) =
      f.cosetMap '' (X.inducedComponent '' s) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  exact f.inducedComponent_inducedMap z

theorem finite_inducedComponent_image_inducedMap (f : X ⟶ Y)
    {s : Set X.InducedSpectrum} (hs : (X.inducedComponent '' s).Finite) :
    (Y.inducedComponent '' (f.inducedMap '' s)).Finite := by
  rw [f.inducedComponent_image_inducedMap]
  exact hs.image f.cosetMap

end Hom

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
