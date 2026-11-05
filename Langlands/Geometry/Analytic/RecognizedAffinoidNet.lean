import Langlands.Geometry.Analytic.RecognizedAffinoidCategory

/-! # The constructed net of recognized affinoid subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Filter Topology
open scoped Topology

namespace AtlasTopology

variable {X : Type v} [TopologicalSpace X] {τ : Set (Set X)}

/-- A finite closed covering is a quasinet: retain exactly its members
containing the given point and exclude the finite union of the others. -/
theorem isQuasinet_of_finite_closedCover (σ : Set (Set X))
    (hσ : σ.Finite) (hστ : σ ⊆ τ) (hclosed : ∀ S ∈ σ, IsClosed S)
    (hcover : ⋃₀ σ = Set.univ) : IsQuasinet τ := by
  classical
  intro x
  let good := {S ∈ σ | x ∈ S}
  let bad := {S ∈ σ | x ∉ S}
  have hbad : bad.Finite := hσ.subset (fun _ h => h.1)
  have hbadclosed : IsClosed (⋃₀ bad) :=
    hbad.isClosed_sUnion (fun S hS => hclosed S hS.1)
  have hx : x ∈ (⋃₀ bad)ᶜ := by
    rintro ⟨S, hS, hxS⟩
    exact hS.2 hxS
  refine ⟨good, hσ.subset (fun _ h => h.1), ?_, ?_, ?_⟩
  · intro S hS
    exact hστ hS.1
  · intro S hS
    exact hS.2
  · apply Filter.mem_of_superset (hbadclosed.isOpen_compl.mem_nhds hx)
    intro y hy
    have hycover : y ∈ ⋃₀ σ := hcover.symm ▸ Set.mem_univ y
    obtain ⟨S, hS, hyS⟩ := hycover
    have hxS : x ∈ S := by
      by_contra h
      exact hy ⟨S, ⟨hS, h⟩, hyS⟩
    exact ⟨S, ⟨hS, hxS⟩, hyS⟩

end AtlasTopology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

namespace FiniteChartGluingData

variable {a} (d : FiniteChartGluingData a)

/-- On a Hausdorff finite union, its finite original-chart cover consists
of closed relative subsets and therefore gives a contained-member quasinet. -/
theorem isQuasinet_restrictedChartFamily [T2Space d.locus] :
    AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily
        (Set.range (fun i => Set.range (a.chart i))) d.locus) := by
  let f (i : Fin d.size) : Set d.locus :=
    Subtype.val ⁻¹' Set.range (a.chart (d.index i))
  apply AtlasTopology.isQuasinet_of_finite_closedCover
    (Set.range f) (Set.finite_range f)
  · rintro S ⟨i, rfl⟩
    exact ⟨Set.range (a.chart (d.index i)), Set.mem_range_self _,
      fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
  · rintro S ⟨i, rfl⟩
    have hc : IsCompact (f i) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage'
        (isCompact_range (a.isEmbedding_chart (d.index i)).continuous)
        (by
          simpa only [Subtype.range_coe, locus] using
            (Set.subset_iUnion (fun j => Set.range (a.chart (d.index j))) i))
    exact hc.isClosed
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

end FiniteChartGluingData

namespace SpecialSubset

variable {a} (W : a.SpecialSubset)

theorem isQuasinet_restrictedChartFamily :
    AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily
        (Set.range (fun i => Set.range (a.chart i))) W.val) := by
  rw [← W.gluingData_locus]
  exact W.gluingData.isQuasinet_restrictedChartFamily

end SpecialSubset

namespace RecognizedSubset

/-- The literal family of recognized subsets, before packaging any atlas
domain-representation property on their mutual inclusions. -/
def family : Set (Set X) := Set.range (fun U : a.RecognizedSubset => U.locus)

theorem chartFamily_subset_family :
    Set.range (fun i => Set.range (a.chart i)) ⊆ family a := by
  rintro S ⟨i, rfl⟩
  exact ⟨⟨SpecialSubset.original a i, SpecialSubset.original_isRecognized a i⟩, rfl⟩

/-- The pairwise intersection axiom follows from relative refinement by
original net members inside each finite Hausdorff special union. -/
theorem isNet_family : AtlasTopology.IsNet (family a) := by
  refine ⟨a.isNet_chartFamily.1.mono (chartFamily_subset_family a), ?_⟩
  rintro S ⟨U, rfl⟩ T ⟨V, rfl⟩
  have h := a.isNet_chartFamily.isQuasinet_restrictedFamily_inter
    U.val.isQuasinet_restrictedChartFamily V.val.isQuasinet_restrictedChartFamily
  apply h.mono
  rintro Q ⟨R, hR, hsub, rfl⟩
  exact ⟨R, chartFamily_subset_family a hR, hsub, rfl⟩

/-- The chart family has exactly the original literal recognized members. -/
theorem chartFamily_eq_family :
    Set.range (fun U : a.RecognizedSubset => Set.range U.chart) = family a := by
  exact congrArg Set.range (funext fun U : a.RecognizedSubset => U.range_chart)

theorem isNet_chartFamily :
    AtlasTopology.IsNet (Set.range (fun U : a.RecognizedSubset => Set.range U.chart)) := by
  rw [chartFamily_eq_family a]
  exact isNet_family a

end RecognizedSubset

/-- The source full-net recognition family is an actual net, by applying
the proved construction to the already constructed enlarged atlas. -/
theorem isNet_recognizedAffinoidFamily :
    AtlasTopology.IsNet a.recognizedAffinoidFamily :=
  RecognizedSubset.isNet_family a.saturatedAtlas

end IndexedAffinoidAtlas
end Langlands.Analytic
