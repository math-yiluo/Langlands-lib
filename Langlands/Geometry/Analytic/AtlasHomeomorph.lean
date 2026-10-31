import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph
import Langlands.Geometry.Analytic.ChosenAtlasMorphisms

/-! # Transport of arbitrary supplied affinoid atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set Topology CategoryTheory
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {Y : Type z} [TopologicalSpace Y] (e : X ≃ₜ Y)

/-- Keep the actual affinoid algebra and compose its chart with the homeomorphism. -/
def transportChart (i : a.Index) : BanachSpectrum (a.algebra i) → Y :=
  e ∘ a.chart i

theorem range_transportChart (i : a.Index) :
    Set.range (a.transportChart e i) = e '' Set.range (a.chart i) :=
  Set.range_comp e (a.chart i)

theorem preimage_range_transportChart (i : a.Index) :
    e ⁻¹' Set.range (a.transportChart e i) = Set.range (a.chart i) := by
  rw [a.range_transportChart, e.preimage_image]

theorem chart_subset_of_transportSubset (i j : a.Index)
    (h : Set.range (a.transportChart e i) ⊆ Set.range (a.transportChart e j)) :
    Set.range (a.chart i) ⊆ Set.range (a.chart j) := by
  rw [← a.preimage_range_transportChart e i, ← a.preimage_range_transportChart e j]
  exact Set.preimage_mono h

theorem transportChart_subset (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    Set.range (a.transportChart e i) ⊆ Set.range (a.transportChart e j) := by
  rw [a.range_transportChart, a.range_transportChart]
  exact Set.image_mono h

theorem transportChartFamily_eq :
    Set.range (fun i => Set.range (a.transportChart e i)) =
      AtlasTopology.imageFamily e (Set.range (fun i => Set.range (a.chart i))) := by
  ext U
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Set.range (a.chart i), ⟨i, rfl⟩, (a.range_transportChart e i).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, a.range_transportChart e i⟩

theorem isNet_transportChartFamily :
    AtlasTopology.IsNet (Set.range (fun i => Set.range (a.transportChart e i))) := by
  rw [a.transportChartFamily_eq]
  exact a.isNet_chartFamily.imageFamily e

/-- The original bounded restriction, using the pulled-back chart containment. -/
def transportRestriction (i j : a.Index)
    (h : Set.range (a.transportChart e i) ⊆ Set.range (a.transportChart e j)) :
    BoundedAlgHom K (a.algebra j) (a.algebra i) :=
  a.restriction i j (a.chart_subset_of_transportSubset e i j h)

theorem transportRestriction_chart (i j : a.Index)
    (h : Set.range (a.transportChart e i) ⊆ Set.range (a.transportChart e j))
    (x : BanachSpectrum (a.algebra i)) :
    a.transportChart e j
        (BanachSpectrum.comap (a.transportRestriction e i j h).toBoundedRingHom x) =
      a.transportChart e i x :=
  congrArg e (a.restriction_chart i j _ x)

/-- Full presented-affinoid-test factorization is retained, including
empty and nonstrict test spectra. -/
theorem transportRestriction_universal (i j : a.Index)
    (h : Set.range (a.transportChart e i) ⊆ Set.range (a.transportChart e j))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : ∀ x : BanachSpectrum R,
      a.transportChart e j (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        Set.range (a.transportChart e i)) :
    ∃! ψ : BoundedAlgHom K (a.algebra i) R,
      ψ.comp (a.transportRestriction e i j h) = φ := by
  apply a.restriction_universal i j _ R φ
  intro x
  obtain ⟨y, hy⟩ := hφ x
  exact ⟨y, e.injective hy⟩

/-- Construct the target atlas; only a topological target and a homeomorphism
are supplied. Chart indices, algebras and bounded restrictions are retained. -/
def transport : IndexedAffinoidAtlas.{u, z, w} K Y where
  Index := a.Index
  algebra := a.algebra
  chart := a.transportChart e
  isEmbedding_chart i := e.isEmbedding.comp (a.isEmbedding_chart i)
  chartDomain_injective := by
    intro i j h
    apply a.chartDomain_injective
    change Set.range (a.chart i) = Set.range (a.chart j)
    change Set.range (a.transportChart e i) = Set.range (a.transportChart e j) at h
    rw [← a.preimage_range_transportChart e i,
      ← a.preimage_range_transportChart e j, h]
  locallyHausdorff y := by
    obtain ⟨U, hU, hT2⟩ := a.locallyHausdorff (e.symm y)
    let : T2Space U := hT2
    refine ⟨e '' U, ?_, (e.image U).t2Space⟩
    simpa only [e.apply_symm_apply] using e.isOpenMap.image_mem_nhds hU
  isNet_chartFamily := a.isNet_transportChartFamily e
  restriction := a.transportRestriction e
  restriction_chart := a.transportRestriction_chart e
  restriction_universal := a.transportRestriction_universal e
  restriction_id i h := a.restriction_id i _
  restriction_comp i j k hij hjk hik := a.restriction_comp i j k _ _ _

@[simp]
theorem transport_algebra (i : a.Index) : (a.transport e).algebra i = a.algebra i := rfl

@[simp]
theorem transport_chart (i : a.Index) (x : BanachSpectrum (a.algebra i)) :
    (a.transport e).chart i x = e (a.chart i x) := rfl

@[simp]
theorem transport_restriction (i j : a.Index)
    (h : Set.range ((a.transport e).chart i) ⊆ Set.range ((a.transport e).chart j)) :
    (a.transport e).restriction i j h =
      a.restriction i j (a.chart_subset_of_transportSubset e i j h) := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)
  {Y : Type v} [TopologicalSpace Y] (e : A.space ≃ₜ Y)

/-- The supplied atlas transported to the homeomorphic target. -/
def transport : AffinoidAtlasPresentation.{u, v, w} K where
  space := TopCat.of Y
  atlas := A.atlas.transport e

/-- The homeomorphism with identity chart indices and bounded identity pullbacks. -/
def transportHom : A ⟶ A.transport e where
  baseMap := ⟨e, e.continuous⟩
  indexMap := _root_.id
  index_mono := A.atlas.transportChart_subset e
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- The inverse homeomorphism uses the same genuine chart algebras. -/
def transportInv : A.transport e ⟶ A where
  baseMap := ⟨e.symm, e.symm.continuous⟩
  indexMap := _root_.id
  index_mono := A.atlas.chart_subset_of_transportSubset e
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i)
  chart_comm i x := (e.symm_apply_apply (A.atlas.chart i x)).symm
  restriction_comm _ _ _ := rfl

/-- An actual isomorphism in the category of monotone chosen atlas maps. -/
def transportIso : A ≅ A.transport e where
  hom := A.transportHom e
  inv := A.transportInv e
  hom_inv_id := Hom.ext (ContinuousMap.ext fun x => e.symm_apply_apply x)
    rfl (heq_of_eq (funext fun _ => rfl))
  inv_hom_id := Hom.ext (ContinuousMap.ext fun y => e.apply_symm_apply y)
    rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem transportIso_hom_apply (x : A.space) :
    (A.transportIso e).hom.baseMap x = e x := rfl

@[simp]
theorem transportIso_inv_apply (y : Y) :
    (A.transportIso e).inv.baseMap y = e.symm y := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
