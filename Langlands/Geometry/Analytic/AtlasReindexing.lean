import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms

/-! # Transport of actual atlases along index equivalences -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) {J : Type z} (e : J ≃ a.Index)

theorem reindexed_chartFamily :
    Set.range (fun j : J => Set.range (a.chart (e j))) =
      Set.range (fun i => Set.range (a.chart i)) := by
  ext U
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨e j, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i,
      congrArg (fun k => Set.range (a.chart k)) (e.apply_symm_apply i)⟩

/-- Change only the names and universe of chart indices. The actual space,
algebras, charts and entire bounded restrictions are retained. -/
def reindex : IndexedAffinoidAtlas.{u, v, z} K X where
  Index := J
  algebra j := a.algebra (e j)
  chart j := a.chart (e j)
  isEmbedding_chart j := a.isEmbedding_chart (e j)
  chartDomain_injective i j h := e.injective (a.chartDomain_injective h)
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := by
    rw [a.reindexed_chartFamily e]
    exact a.isNet_chartFamily
  restriction i j h := a.restriction (e i) (e j) h
  restriction_chart i j h x := a.restriction_chart (e i) (e j) h x
  restriction_universal i j h R φ hφ :=
    a.restriction_universal (e i) (e j) h R φ hφ
  restriction_id i h := a.restriction_id (e i) h
  restriction_comp i j k hij hjk hik :=
    a.restriction_comp (e i) (e j) (e k) hij hjk hik

@[simp]
theorem reindex_algebra (j : J) : (a.reindex e).algebra j = a.algebra (e j) := rfl

@[simp]
theorem reindex_chart (j : J) : (a.reindex e).chart j = a.chart (e j) := rfl

@[simp]
theorem reindex_restriction (i j : J)
    (h : Set.range (a.chart (e i)) ⊆ Set.range (a.chart (e j))) :
    (a.reindex e).restriction i j h = a.restriction (e i) (e j) h := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

/-- A presentation keeps its literal topological space under reindexing. -/
def reindex (A : AffinoidAtlasPresentation.{u, v, w} K) {J : Type z}
    (e : J ≃ A.atlas.Index) : AffinoidAtlasPresentation.{u, v, z} K where
  space := A.space
  atlas := A.atlas.reindex e

@[simp]
theorem reindex_space (A : AffinoidAtlasPresentation.{u, v, w} K) {J : Type z}
    (e : J ≃ A.atlas.Index) : (A.reindex e).space = A.space := rfl

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {I J : Type z} (eA : I ≃ A.atlas.Index) (eB : J ≃ B.atlas.Index)

/-- Transport every admissible bounded pullback, with no choice of a
preferred target chart and no change to the continuous map. -/
def reindex (f : StrongHom A B) : StrongHom (A.reindex eA) (B.reindex eB) where
  baseMap := f.baseMap
  target_exists i := by
    obtain ⟨j, hj⟩ := f.target_exists (eA i)
    refine ⟨eB.symm j, ?_⟩
    change f.baseMap '' Set.range (A.atlas.chart (eA i)) ⊆
      Set.range (B.atlas.chart (eB (eB.symm j)))
    rw [eB.apply_symm_apply]
    exact hj
  pullback i j h := f.pullback (eA i) (eB j) h
  chart_comm i j h x := f.chart_comm (eA i) (eB j) h x
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm (eA i) (eA i') (eB j) (eB j') hi hj h h'

@[simp]
theorem reindex_baseMap (f : StrongHom A B) :
    (f.reindex eA eB).baseMap = f.baseMap := rfl

@[simp]
theorem reindex_pullback (f : StrongHom A B) (i : I) (j : J)
    (h : f.baseMap '' Set.range (A.atlas.chart (eA i)) ⊆
      Set.range (B.atlas.chart (eB j))) :
    (f.reindex eA eB).pullback i j h = f.pullback (eA i) (eB j) h := rfl

@[simp]
theorem reindex_chartImageLocus (f : StrongHom A B) (i : I) (j : J) :
    (f.reindex eA eB).chartImageLocus i j = f.chartImageLocus (eA i) (eB j) := rfl

/-- Full affinoid-test representation survives a change of index universe. -/
theorem IsQuasiIso.reindex {f : StrongHom A B} (hf : f.IsQuasiIso) :
    (f.reindex eA eB).IsQuasiIso :=
  ⟨hf.1, fun i j h => hf.2 (eA i) (eB j) h⟩

theorem isQuasiIso_reindex_iff (f : StrongHom A B) :
    (f.reindex eA eB).IsQuasiIso ↔ f.IsQuasiIso := by
  constructor
  · rintro ⟨hb, hp⟩
    refine ⟨hb, ?_⟩
    intro i j h
    obtain ⟨i, rfl⟩ := eA.surjective i
    obtain ⟨j, rfl⟩ := eB.surjective j
    exact hp i j h
  · exact fun hf => hf.reindex eA eB

end StrongHom
end AffinoidAtlasPresentation
end Langlands.Analytic
