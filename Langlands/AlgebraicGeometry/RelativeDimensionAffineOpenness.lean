import Langlands.AlgebraicGeometry.FiberDimensionLocalCharts
import Langlands.AlgebraicGeometry.RelativeDimensionSublevelStatement
import Mathlib.Topology.LocalAtTarget

/-! # Affine relative fibre dimension and open source charts -/

noncomputable section

universe u v w

open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Restricting an actual point fibre along an open source embedding preserves
its local topological dimension at each lifted point. -/
theorem topologicalKrullDimAt_fiber_openEmbedding
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (i : Z → X) (hi : IsOpenEmbedding i) (z : Z) :
    topologicalKrullDimAt (⟨z, rfl⟩ : (f ∘ i) ⁻¹' {f (i z)}) =
      topologicalKrullDimAt (⟨i z, rfl⟩ : f ⁻¹' {f (i z)}) :=
  topologicalKrullDimAt_eq_of_isOpenEmbedding
    (Set.restrictPreimage_isOpenEmbedding (f ⁻¹' {f (i z)}) hi)
    (⟨z, rfl⟩ : i ⁻¹' (f ⁻¹' {f (i z)}))

private def affineFiberDimension
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  topologicalKrullDimAt
    (⟨q, rfl⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)})

private theorem affineFiberDimension_eq
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    affineFiberDimension R S q =
      topologicalKrullDimAt
        ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))) ⟨q, rfl⟩) :=
  topologicalKrullDimAt_homeomorph _ _

private theorem affineFiberDimension_le
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    affineFiberDimension R S q ≤ ringKrullDim ((q.comap (algebraMap R S)).asIdeal.Fiber S) :=
  (affineFiberDimension_eq R S q).trans_le
    ((topologicalKrullDimAt_le _).trans_eq
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _))

private theorem affineFiberDimension_chart
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {q : PrimeSpectrum S} (d : FiberDimensionLocalChart R S q)
    (z : PrimeSpectrum (Localization.Away d.chart.element)) :
    affineFiberDimension R (Localization.Away d.chart.element) z =
      affineFiberDimension R S (d.sourceMap z) := by
  have he : PrimeSpectrum.comap (algebraMap R S) ∘ d.sourceMap =
      PrimeSpectrum.comap (algebraMap R (Localization.Away d.chart.element)) := by
    ext z
    simp only [FiberDimensionLocalChart.sourceMap, Function.comp_apply,
      ← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]
  have h := topologicalKrullDimAt_fiber_openEmbedding
    (PrimeSpectrum.comap (algebraMap R S)) d.sourceMap d.sourceMap_isOpenEmbedding z
  have he' := congrArg
    (fun g : PrimeSpectrum (Localization.Away d.chart.element) → PrimeSpectrum R =>
      topologicalKrullDimAt (⟨z, rfl⟩ : g ⁻¹' {g z})) he
  exact he'.symm.trans h

/-- Every natural sublevel of the actual local residue-field fibre dimension
of an affine finite-type morphism is open. -/
theorem isOpen_affine_fiber_dimension_sublevel
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (n : ℕ) :
    IsOpen {q : PrimeSpectrum S |
      topologicalKrullDimAt
        ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
          ⟨q, rfl⟩) ≤ (n : WithBot ℕ∞)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  let d := fiberDimensionLocalChart R S q
  refine ⟨Set.range d.sourceMap, ?_, d.sourceMap_isOpenEmbedding.isOpen_range,
    d.mem_range_sourceMap⟩
  rintro _ ⟨z, rfl⟩
  exact (affineFiberDimension_eq R S (d.sourceMap z)).symm.trans_le
    ((affineFiberDimension_chart d z).symm.trans_le
      ((affineFiberDimension_le R _ z).trans ((d.fiber_dimension_le _).trans hq)))

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
