import Langlands.Geometry.Analytic.AtlasMapChartChange

/-! # Universal factorization and naturality of target-chart change -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A chart change preserves every bounded factorization through a common
original subchart, after every bounded affinoid coefficient change. -/
def IsMapChartChange (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (ψ : BoundedAlgHom K (a.algebra j) R) : Prop :=
  ∀ (T : PresentedAffinoidAlgebra K) (η : BoundedAlgHom K R T)
    (m : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (hmj : Set.range (a.chart m) ⊆ Set.range (a.chart j))
    (α : BoundedAlgHom K (a.algebra m) T),
    α.comp (a.restriction m i hmi) = η.comp φ →
      η.comp ψ = α.comp (a.restriction m j hmj)

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {S : Set X}
  (c : a.CompactIntersectionChartCover i j S)
  (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
  (hφ : ∀ x : BanachSpectrum R,
    a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ S)

/-- Pull back the actual finite source cover once more along an arbitrary
bounded coefficient map, retaining its entire new test spectrum as target. -/
def mapTestCover (T : PresentedAffinoidAlgebra K) (η : BoundedAlgHom K R T) :
    Domain.FiniteCover (Domain.whole K T) where
  size := c.size
  obj t := Domain.pullback η ((c.mapPullbackCover R φ hφ).obj t)
  map t := ⟨(Domain.pullback η ((c.mapPullbackCover R φ hφ).obj t)).baseMap,
    BoundedAlgHom.comp_id _⟩
  covers x _ := (c.mapPullbackCover R φ hφ).covers
    (BanachSpectrum.comap η.toBoundedRingHom x) (Set.mem_univ _)

/-- Every factorization on an arbitrary affinoid test is preserved by the
constructed target-chart change, as an equality of complete bounded maps. -/
theorem glueMapChartChange_test (T : PresentedAffinoidAlgebra K)
    (η : BoundedAlgHom K R T) (m : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (hmj : Set.range (a.chart m) ⊆ Set.range (a.chart j))
    (α : BoundedAlgHom K (a.algebra m) T)
    (hα : α.comp (a.restriction m i hmi) = η.comp φ) :
    η.comp (c.glueMapChartChange R φ hφ) = α.comp (a.restriction m j hmj) := by
  have hlocal (t : Fin c.size) :
      ((c.mapTestCover R φ hφ T η).map t).restriction.comp
          (η.comp (c.glueMapChartChange R φ hφ)) =
        ((c.mapTestCover R φ hφ T η).map t).restriction.comp
          (α.comp (a.restriction m j hmj)) := by
    let D := a.restrictionDomain (c.index t) i (c.left_subset t)
    let Q := Domain.pullback φ D
    let P := Domain.pullback η Q
    let θ := (Domain.pullbackMap η Q).comp (Domain.pullbackMap φ D)
    let β := P.baseMap.comp α
    have hθ : θ.comp (a.restriction (c.index t) i (c.left_subset t)) =
        P.baseMap.comp (η.comp φ) := by
      change ((Domain.pullbackMap η Q).comp (Domain.pullbackMap φ D)).comp D.baseMap =
        P.baseMap.comp (η.comp φ)
      rw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
        ← BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
        BoundedAlgHom.comp_assoc]
    have hβ : β.comp (a.restriction m i hmi) = P.baseMap.comp (η.comp φ) := by
      change (P.baseMap.comp α).comp (a.restriction m i hmi) = _
      rw [BoundedAlgHom.comp_assoc, hα]
    have hover := a.originalChartRestriction_test_overlap i j (c.index t) m
      (c.left_subset t) (c.right_subset t) hmi hmj P.algebra θ β
      (hθ.trans hβ.symm)
    change P.baseMap.comp (η.comp (c.glueMapChartChange R φ hφ)) =
      P.baseMap.comp (α.comp (a.restriction m j hmj))
    calc
      P.baseMap.comp (η.comp (c.glueMapChartChange R φ hφ)) =
          ((Domain.pullbackMap η Q).comp Q.baseMap).comp
            (c.glueMapChartChange R φ hφ) := by
        rw [Domain.pullbackMap_comp_baseMap, BoundedAlgHom.comp_assoc]
      _ = (Domain.pullbackMap η Q).comp (c.mapPullbackFamily R φ hφ t) :=
        congrArg (fun q => (Domain.pullbackMap η Q).comp q)
          (c.glueMapChartChange_local R φ hφ t)
      _ = θ.comp (a.restriction (c.index t) j (c.right_subset t)) := rfl
      _ = β.comp (a.restriction m j hmj) := hover
      _ = P.baseMap.comp (α.comp (a.restriction m j hmj)) := rfl
  apply BoundedAlgHom.ext
  intro b
  apply (c.mapTestCover R φ hφ T η).algebra_ext_of_restrict_eq
  intro t
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    ((c.mapTestCover R φ hφ T η).obj t).algebra => q b) (hlocal t)

/-- The actual bounded descent satisfies the universal factorization law. -/
theorem glueMapChartChange_isMapChartChange :
    a.IsMapChartChange i j R φ (c.glueMapChartChange R φ hφ) :=
  c.glueMapChartChange_test R φ hφ

/-- The universal factorization law determines the complete bounded map.
It forces the original descent equations on the actual source cover. -/
theorem eq_glueMapChartChange (ψ : BoundedAlgHom K (a.algebra j) R)
    (hψ : a.IsMapChartChange i j R φ ψ) :
    ψ = c.glueMapChartChange R φ hφ := by
  apply (c.mapPullbackCover R φ hφ).glueBoundedAlgHom_unique
    (c.mapPullbackFamily R φ hφ) (c.mapPullbackFamily_compatible R φ hφ) ψ
  intro t
  exact hψ ((c.mapPullbackCover R φ hφ).obj t).algebra
    ((c.mapPullbackCover R φ hφ).obj t).baseMap
    (c.index t) (c.left_subset t) (c.right_subset t)
    (Domain.pullbackMap φ (a.restrictionDomain (c.index t) i (c.left_subset t)))
    (Domain.pullbackMap_comp_baseMap φ _)

/-- All finite common-chart covers give literally the same bounded map. -/
theorem glueMapChartChange_eq {S' : Set X}
    (d : a.CompactIntersectionChartCover i j S')
    (hφ' : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ S') :
    c.glueMapChartChange R φ hφ = d.glueMapChartChange R φ hφ' :=
  d.eq_glueMapChartChange R φ hφ' _ (c.glueMapChartChange_isMapChartChange R φ hφ)

end CompactIntersectionChartCover

/-- The chosen image cover constructs the map characterized by all tests. -/
theorem changeMapChart_isMapChartChange (i j : a.Index)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.IsMapChartChange i j R φ (a.changeMapChart i j R φ h) :=
  (a.mapImageChartCover i j R φ h).glueMapChartChange_isMapChartChange R φ
    (fun x => ⟨x, rfl⟩)

/-- Uniqueness against the canonical bounded chart-change construction. -/
theorem eq_changeMapChart (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (ψ : BoundedAlgHom K (a.algebra j) R) (hψ : a.IsMapChartChange i j R φ ψ) :
    ψ = a.changeMapChart i j R φ h :=
  (a.mapImageChartCover i j R φ h).eq_glueMapChartChange R φ
    (fun x => ⟨x, rfl⟩) ψ hψ

/-- Bounded coefficient change preserves the universal factorization law. -/
theorem IsMapChartChange.comp {i j : a.Index} {R T : PresentedAffinoidAlgebra K}
    {φ : BoundedAlgHom K (a.algebra i) R}
    {ψ : BoundedAlgHom K (a.algebra j) R}
    (hψ : a.IsMapChartChange i j R φ ψ) (η : BoundedAlgHom K R T) :
    a.IsMapChartChange i j T (η.comp φ) (η.comp ψ) := by
  intro U ζ m hmi hmj α hα
  exact hψ U (ζ.comp η) m hmi hmj α hα

/-- The constructed map commutes with every bounded affinoid coefficient map. -/
theorem changeMapChart_comp (i j : a.Index) (R T : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (η : BoundedAlgHom K R T)
    (hη : ∀ x : BanachSpectrum T,
      a.chart i (BanachSpectrum.comap (η.comp φ).toBoundedRingHom x) ∈
        Set.range (a.chart j)) :
    a.changeMapChart i j T (η.comp φ) hη =
      η.comp (a.changeMapChart i j R φ h) :=
  (a.eq_changeMapChart i j T (η.comp φ) hη _
    ((a.changeMapChart_isMapChartChange i j R φ h).comp a η)).symm

/-- Changing a map within its original chart recovers the original bounded map. -/
theorem changeMapChart_self (i : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart i)) :
    a.changeMapChart i i R φ h = φ := by
  symm
  apply a.eq_changeMapChart i i R φ h
  intro T η m hmi hmj α hα
  exact hα.symm

/-- If the new chart contains the old one, chart change is the original bounded
restriction followed by the supplied map. -/
theorem changeMapChart_of_subset (i j : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.changeMapChart i j R φ h = φ.comp (a.restriction i j hij) := by
  symm
  apply a.eq_changeMapChart i j R φ h
  intro T η m hmi hmj α hα
  calc
    η.comp (φ.comp (a.restriction i j hij)) =
        (α.comp (a.restriction m i hmi)).comp (a.restriction i j hij) :=
      congrArg (fun q => q.comp (a.restriction i j hij)) hα.symm
    _ = α.comp (a.restriction m j hmj) := by
      rw [BoundedAlgHom.comp_assoc, ← a.restriction_comp m i j hmi hij hmj]

end Langlands.Analytic.IndexedAffinoidAtlas
