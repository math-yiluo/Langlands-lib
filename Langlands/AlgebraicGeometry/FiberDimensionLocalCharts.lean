import Langlands.AlgebraicGeometry.FiberDimensionPrincipalCharts
import Langlands.AlgebraicGeometry.LocalTopologicalDimension
import Langlands.AlgebraicGeometry.AffineOpenDimension
import Mathlib.RingTheory.Localization.BaseChange

/-! # Principal neighbourhoods realizing local fibre dimension -/

universe u v

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open Algebra TensorProduct Topology TopologicalSpace

/-- A principal source neighbourhood realizes the local dimension in the
actual residue-field fibre. No finite-type hypothesis is needed here. -/
theorem exists_away_fiber_dimension_eq_at
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) = p) :
    ∃ r : S, r ∉ q.asIdeal ∧
      ringKrullDim (p.asIdeal.Fiber (Localization.Away r)) =
        topologicalKrullDimAt ((PrimeSpectrum.preimageHomeomorphFiber R S p) ⟨q, hq⟩) := by
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  let x := e ⟨q, hq⟩
  obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_at x
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen x hxU
  obtain ⟨a, hap, r, har⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal f
  have ha : IsUnit (algebraMap R (p.asIdeal.Fiber S) a) := by
    rw [IsScalarTower.algebraMap_eq R p.asIdeal.ResidueField (p.asIdeal.Fiber S)]
    exact (isUnit_iff_ne_zero.mpr
      (fun h => hap (Ideal.algebraMap_residueField_eq_zero.mp h))).map
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
  have hb : PrimeSpectrum.basicOpen ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r) =
      PrimeSpectrum.basicOpen f := by
    ext z
    change ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r) ∉ z.asIdeal ↔ f ∉ z.asIdeal
    rw [← har, Algebra.smul_def]
    exact not_congr (z.asIdeal.unit_mul_mem_iff_mem ha)
  have hxr : x ∈ PrimeSpectrum.basicOpen ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r) := by
    rwa [hb]
  have hxq : x.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    congrArg Subtype.val (e.symm_apply_apply ⟨q, hq⟩)
  have hrq : r ∉ q.asIdeal := by
    rw [← hxq]
    exact hxr
  have hdim : topologicalKrullDim
      (PrimeSpectrum.basicOpen ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r)) =
      topologicalKrullDimAt x := by
    rw [hb]
    apply le_antisymm
    · exact ((Topology.IsEmbedding.inclusion hfU).isInducing.topologicalKrullDim_le).trans_eq hU
    · exact topologicalKrullDimAt_le_open x (PrimeSpectrum.basicOpen f) hxf
  refine ⟨r, hrq, ?_⟩
  calc
    ringKrullDim (p.asIdeal.Fiber (Localization.Away r)) =
        ringKrullDim (Localization.Away ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r)) :=
      (IsLocalization.Away.tensorProductEquivTMulRight R p.asIdeal.ResidueField r
        (Localization.Away r)).toRingEquiv.ringKrullDim
    _ = topologicalKrullDim
        (PrimeSpectrum.basicOpen ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] r)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm.trans
        ((localizationAwayBasicOpenHomeomorph _).isHomeomorph.topologicalKrullDim_eq _)
    _ = topologicalKrullDimAt x := hdim

/-- Two successive principal neighbourhoods of a source point, with a
polynomial chart whose rank is the original local fibre dimension. -/
structure FiberDimensionLocalChart
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) where
  firstElement : S
  first_not_mem : firstElement ∉ q.asIdeal
  firstPoint : PrimeSpectrum (Localization.Away firstElement)
  firstPoint_eq : firstPoint.comap (algebraMap S (Localization.Away firstElement)) = q
  chart : FiberDimensionPrincipalChart R (Localization.Away firstElement) firstPoint
  rank_eq : (chart.rank : WithBot ℕ∞) =
    topologicalKrullDimAt
      ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))) ⟨q, rfl⟩)

/-- Construct an actual iterated principal chart whose fibres have dimension
uniformly bounded by the local dimension at the original source point. -/
noncomputable def fiberDimensionLocalChart
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    FiberDimensionLocalChart R S q := by
  classical
  apply Classical.choice
  let p := q.comap (algebraMap R S)
  obtain ⟨r, hr, hdim⟩ := exists_away_fiber_dimension_eq_at R S p q rfl
  let e := localizationAwayBasicOpenHomeomorph r
  let q' := e.symm ⟨q, hr⟩
  have hq' : q'.comap (algebraMap S (Localization.Away r)) = q := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨q, hr⟩)
  have hp : q'.comap (algebraMap R (Localization.Away r)) = p := by
    rw [IsScalarTower.algebraMap_eq R S (Localization.Away r), PrimeSpectrum.comap_comp]
    change (q'.comap (algebraMap S (Localization.Away r))).comap (algebraMap R S) = p
    rw [hq']
  let d := fiberDimensionPrincipalChart R (Localization.Away r) q'
  have heq : (d.rank : WithBot ℕ∞) =
      topologicalKrullDimAt ((PrimeSpectrum.preimageHomeomorphFiber R S p) ⟨q, rfl⟩) := by
    rw [← d.dimension_eq, hp]
    exact hdim
  exact ⟨
    { firstElement := r
      first_not_mem := hr
      firstPoint := q'
      firstPoint_eq := hq'
      chart := d
      rank_eq := heq }⟩

namespace FiberDimensionLocalChart

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {q : PrimeSpectrum S} (d : FiberDimensionLocalChart R S q)

/-- The actual map from the iterated localized chart to the original source. -/
def sourceMap :
    PrimeSpectrum (Localization.Away d.chart.element) → PrimeSpectrum S :=
  PrimeSpectrum.comap (algebraMap S (Localization.Away d.firstElement)) ∘
    PrimeSpectrum.comap
      (algebraMap (Localization.Away d.firstElement) (Localization.Away d.chart.element))

theorem sourceMap_isOpenEmbedding : IsOpenEmbedding d.sourceMap :=
  (PrimeSpectrum.localization_away_isOpenEmbedding _ d.firstElement).comp
    (PrimeSpectrum.localization_away_isOpenEmbedding _ d.chart.element)

theorem mem_range_sourceMap : q ∈ Set.range d.sourceMap := by
  let e := localizationAwayBasicOpenHomeomorph d.chart.element
  refine ⟨e.symm ⟨d.firstPoint, d.chart.not_mem⟩, ?_⟩
  have h : (e.symm ⟨d.firstPoint, d.chart.not_mem⟩).comap
      (algebraMap (Localization.Away d.firstElement) (Localization.Away d.chart.element)) =
        d.firstPoint :=
    congrArg Subtype.val (e.apply_symm_apply ⟨d.firstPoint, d.chart.not_mem⟩)
  change PrimeSpectrum.comap (algebraMap S (Localization.Away d.firstElement))
    (PrimeSpectrum.comap
      (algebraMap (Localization.Away d.firstElement) (Localization.Away d.chart.element))
        (e.symm ⟨d.firstPoint, d.chart.not_mem⟩)) = q
  rw [h]
  exact d.firstPoint_eq

/-- Every original-base fibre of the actual chart is bounded by the original
local fibre dimension at the chosen point. -/
theorem fiber_dimension_le (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber (Localization.Away d.chart.element)) ≤
      topologicalKrullDimAt
        ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))) ⟨q, rfl⟩) :=
  (d.chart.fiber_dimension_le p).trans_eq d.rank_eq

end FiberDimensionLocalChart

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
