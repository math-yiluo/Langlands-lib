import Langlands.Geometry.Analytic.QuasiEtaleCompactCharts

/-! # Finite compact chart covers in the quasi-étale site -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A chart of a chart-domain object that covers its entire underlying space. -/
def chartDomainFullChart (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) :
    (S.domain (S.chartDomain i)).presentation.atlas.Index :=
  ⟨i, Set.Subset.refl _⟩

theorem chartDomainFullChart_surjective (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) :
    Function.Surjective
      ((S.domain (S.chartDomain i)).presentation.atlas.chart (chartDomainFullChart S i)) := by
  intro y
  obtain ⟨x, hx⟩ := y.property
  exact ⟨x, Subtype.ext hx⟩

/-- Compactness selects finitely many actual quasi-étale chart objects from
the local quasi-étale factorizations. -/
theorem IsQuasiEtale.exists_finite_quasiEtale_chart_cover
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    {g : ofSaturation A ⟶ ofSaturation B} (hg : IsQuasiEtale g)
    [CompactSpace A.space] :
    ∃ s : Finset (ofSaturation A).presentation.atlas.Index,
      (∀ i ∈ s, quasiEtale ((ofSaturation A).localizedDomainInclusion
        ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g)) ∧
      ∀ y : A.space, ∃ i ∈ s,
        y ∈ Set.range ((ofSaturation A).presentation.atlas.chart i) := by
  classical
  choose σ hf hn hs using hg.exists_local_quasiEtale_charts
  obtain ⟨t, _, ht⟩ :=
    isCompact_univ.elim_nhds_subcover (fun x => ⋃₀ σ x) (fun x _ => hn x)
  let δ : Set (Set A.space) := ⋃ x ∈ (t : Set A.space), σ x
  have hδ : δ.Finite := t.finite_toSet.biUnion (fun x _ => hf x)
  have hgood : ∀ V : δ, ∃ i : (ofSaturation A).presentation.atlas.Index,
      Set.range ((ofSaturation A).presentation.atlas.chart i) = V.val ∧
        quasiEtale ((ofSaturation A).localizedDomainInclusion
          ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g) := by
    intro V
    obtain ⟨x, _, hx⟩ := Set.mem_iUnion₂.mp V.property
    exact hs x V.val hx
  choose idx hidx hqe using hgood
  let : Fintype δ := hδ.fintype
  refine ⟨Finset.univ.image idx, ?_, ?_⟩
  · intro i hi
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hi
    exact hqe V
  · intro y
    obtain ⟨x, hx, V, hV, hyV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    let W : δ := ⟨V, Set.mem_iUnion₂.mpr ⟨x, hx, hV⟩⟩
    refine ⟨idx W, Finset.mem_image.mpr ⟨W, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hidx W).symm ▸ hyV

end Langlands.Analytic.SaturatedAtlasPresentation
