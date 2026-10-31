import Langlands.Geometry.Analytic.AtlasTopology.DirectedCompact
import Langlands.Geometry.Analytic.CofinalImageStrongInverses

/-! # Strong inverses on nonempty directed affinoid atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A nonempty ambient space supplies an original chart index. -/
theorem nonempty_index [Nonempty X] : Nonempty a.Index := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (a.chart i)) := by
    rw [a.isNet_chartFamily.1.covers]
    exact Set.mem_univ x
  obtain ⟨_, ⟨i, rfl⟩, _⟩ := Set.mem_sUnion.mp hx
  exact ⟨i⟩

/-- A compact subset of a nonempty directed atlas lies inside one chart interior. -/
theorem exists_subset_chart_interior [Nonempty a.Index]
    (hd : a.HasDirectedCharts) {S : Set X} (hS : IsCompact S) :
    ∃ i : a.Index, S ⊆ interior (Set.range (a.chart i)) :=
  a.isNet_chartFamily.1.exists_subset_interior_of_isCompact hd hS

/-- Compact containment uses an original chart, with its original algebra. -/
theorem exists_subset_chart [Nonempty a.Index]
    (hd : a.HasDirectedCharts) {S : Set X} (hS : IsCompact S) :
    ∃ i : a.Index, S ⊆ Set.range (a.chart i) :=
  a.isNet_chartFamily.1.exists_subset_of_isCompact hd hS

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom.IsQuasiIso

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {f : AffinoidAtlasPresentation.StrongHom A B} (hf : f.IsQuasiIso)

include hf in
/-- Compact target chart ranges pull back into original directed source charts.
The nonempty-index hypothesis includes the empty compact subset case. -/
theorem hasUpperCofinalImage [Nonempty A.atlas.Index]
    (ha : A.atlas.HasDirectedCharts) : f.HasUpperCofinalImage := by
  intro j
  have hc : IsCompact (hf.inverseBaseMap '' Set.range (B.atlas.chart j)) :=
    (isCompact_range (B.atlas.isEmbedding_chart j).continuous).image
      hf.inverseBaseMap.continuous
  obtain ⟨i, hi⟩ := A.atlas.exists_subset_chart ha hc
  exact ⟨i, (hf.inverse_admissible_iff j i).mp hi⟩

end AffinoidAtlasPresentation.StrongHom.IsQuasiIso

namespace DirectedAtlasPresentation

variable {A B : DirectedAtlasPresentation.{u, v, w} K}

/-- A full quasi-isomorphism out of a directed atlas with an original chart
has a full strong inverse in the actual directed category. -/
def quasiIsoIso [Nonempty A.presentation.atlas.Index]
    (f : A ⟶ B) (hf : f.IsQuasiIso) : A ≅ B :=
  cofinalImageIso f hf (hf.hasUpperCofinalImage A.directed)

@[simp]
theorem quasiIsoIso_hom [Nonempty A.presentation.atlas.Index]
    (f : A ⟶ B) (hf : f.IsQuasiIso) :
    (quasiIsoIso f hf).hom = f := rfl

@[simp]
theorem quasiIsoIso_inv_baseMap [Nonempty A.presentation.atlas.Index]
    (f : A ⟶ B) (hf : f.IsQuasiIso) :
    (quasiIsoIso f hf).inv.baseMap = hf.inverseBaseMap := rfl

/-- Every constructed inverse retains full affinoid-domain representation. -/
theorem quasiIsoIso_inv_isQuasiIso [Nonempty A.presentation.atlas.Index]
    (f : A ⟶ B) (hf : f.IsQuasiIso) :
    (quasiIsoIso f hf).inv.IsQuasiIso :=
  hf.inverse_isQuasiIso B.directed (hf.hasUpperCofinalImage A.directed)

/-- A nonempty underlying source space suffices for the strong isomorphism. -/
def quasiIsoIsoOfNonempty [Nonempty A.presentation.space]
    (f : A ⟶ B) (hf : f.IsQuasiIso) : A ≅ B := by
  letI := A.presentation.atlas.nonempty_index
  exact quasiIsoIso f hf

@[simp]
theorem quasiIsoIsoOfNonempty_hom [Nonempty A.presentation.space]
    (f : A ⟶ B) (hf : f.IsQuasiIso) :
    (quasiIsoIsoOfNonempty f hf).hom = f := rfl

end DirectedAtlasPresentation

end Langlands.Analytic
