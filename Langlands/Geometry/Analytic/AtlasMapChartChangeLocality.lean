import Langlands.Geometry.Analytic.AtlasMapChartChangeNaturality

/-! # Chart compatibility on actual inverse-image affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A R : PresentedAffinoidAlgebra K}

/-- Every bounded test of a domain pullback square factors uniquely through
the actual inverse-image domain. Full domain representation gives the first
factorization; cancellation gives the second complete bounded equation. -/
theorem pullback_test_factorization (φ : BoundedAlgHom K A R) (D : Domain K A)
    (T : PresentedAffinoidAlgebra K) (η : BoundedAlgHom K R T)
    (α : BoundedAlgHom K D.algebra T)
    (hα : α.comp D.baseMap = η.comp φ) :
    ∃! θ : BoundedAlgHom K (pullback φ D).algebra T,
      θ.comp (pullback φ D).baseMap = η ∧
        θ.comp (pullbackMap φ D) = α := by
  have hη : HasImageIn K η (pullback φ D).locus := by
    intro x
    change BanachSpectrum.comap (η.comp φ).toBoundedRingHom x ∈ D.locus
    rw [← hα]
    exact D.represents.hasImageIn (BanachSpectrum.comap α.toBoundedRingHom x)
  obtain ⟨θ, hθ, huniq⟩ := (pullback φ D).represents.2.2 T η hη
  refine ⟨θ, ⟨hθ, ?_⟩, fun ζ hζ => huniq ζ hζ.1⟩
  apply D.represents.hom_ext T
  rw [BoundedAlgHom.comp_assoc, pullbackMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, hθ]
  exact hα.symm

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Two chart maps agree on the actual source inverse image of each common
original target subchart, as equalities of complete bounded algebra maps. -/
def IsLocalMapChartChange (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (ψ : BoundedAlgHom K (a.algebra j) R) : Prop :=
  ∀ (m : a.Index)
    (hmi : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (hmj : Set.range (a.chart m) ⊆ Set.range (a.chart j)),
    (Domain.pullback φ (a.restrictionDomain m i hmi)).baseMap.comp ψ =
      (Domain.pullbackMap φ (a.restrictionDomain m i hmi)).comp
        (a.restriction m j hmj)

/-- Universal coefficient compatibility is exactly the bounded local equation
on the constructed inverse-image domains; arbitrary tests factor through
these full-domain representations. -/
theorem isMapChartChange_iff_local (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (ψ : BoundedAlgHom K (a.algebra j) R) :
    a.IsMapChartChange i j R φ ψ ↔ a.IsLocalMapChartChange i j R φ ψ := by
  constructor
  · intro h m hmi hmj
    exact h (Domain.pullback φ (a.restrictionDomain m i hmi)).algebra
      (Domain.pullback φ (a.restrictionDomain m i hmi)).baseMap m hmi hmj
      (Domain.pullbackMap φ (a.restrictionDomain m i hmi))
      (Domain.pullbackMap_comp_baseMap φ _)
  · intro h T η m hmi hmj α hα
    let D := a.restrictionDomain m i hmi
    obtain ⟨θ, ⟨hθη, hθα⟩, _⟩ := Domain.pullback_test_factorization φ D T η α hα
    calc
      η.comp ψ = (θ.comp (Domain.pullback φ D).baseMap).comp ψ :=
        congrArg (fun q : BoundedAlgHom K R T => q.comp ψ) hθη.symm
      _ = θ.comp ((Domain.pullbackMap φ D).comp (a.restriction m j hmj)) :=
        congrArg (fun q : BoundedAlgHom K (a.algebra j) (Domain.pullback φ D).algebra =>
          θ.comp q) (h m hmi hmj)
      _ = α.comp (a.restriction m j hmj) :=
        congrArg (fun q : BoundedAlgHom K (a.algebra m) T =>
          q.comp (a.restriction m j hmj)) hθα

/-- The actual glued chart change satisfies the geometric local equations. -/
theorem changeMapChart_isLocalMapChartChange (i j : a.Index)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.IsLocalMapChartChange i j R φ (a.changeMapChart i j R φ h) :=
  (a.isMapChartChange_iff_local i j R φ _).mp
    (a.changeMapChart_isMapChartChange i j R φ h)

/-- Local domain equations determine the entire bounded chart change,
whenever its image lies in the new chart. -/
theorem isLocalMapChartChange_iff_eq (i j : a.Index)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (ψ : BoundedAlgHom K (a.algebra j) R) :
    a.IsLocalMapChartChange i j R φ ψ ↔ ψ = a.changeMapChart i j R φ h := by
  constructor
  · intro hψ
    exact a.eq_changeMapChart i j R φ h ψ ((a.isMapChartChange_iff_local i j R φ ψ).mpr hψ)
  · intro hψ
    rw [hψ]
    exact a.changeMapChart_isLocalMapChartChange i j R φ h

end Langlands.Analytic.IndexedAffinoidAtlas
