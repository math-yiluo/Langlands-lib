import Langlands.Geometry.Analytic.DisjointAffinoidAtlas

/-! # Transport of the constructed disjoint affinoid atlas -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.DisjointAffinoidAtlas

open Set Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {I : Type v} (A : I → PresentedAffinoidAlgebra K)
  {X : Type w} [TopologicalSpace X] (e : Space A ≃ₜ X)

/-- The actual spectrum chart followed by the given homeomorphism. -/
def transportChart (c : ChartIndex A) : BanachSpectrum (chartAlgebra A c) → X :=
  e ∘ chart A c

def transportChartDomain (c : ChartIndex A) : Set X :=
  Set.range (transportChart A e c)

def transportChartFamily : Set (Set X) := Set.range (transportChartDomain A e)

theorem isOpenEmbedding_transportChart (c : ChartIndex A) :
    IsOpenEmbedding (transportChart A e c) :=
  e.isOpenEmbedding.comp (isOpenEmbedding_chart A c)

theorem preimage_transportChartDomain (c : ChartIndex A) :
    e ⁻¹' transportChartDomain A e c = chartDomain A c := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, e.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem chartDomain_subset_of_transportSubset (c d : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e d) :
    chartDomain A c ⊆ chartDomain A d := by
  rw [← preimage_transportChartDomain A e c, ← preimage_transportChartDomain A e d]
  exact Set.preimage_mono h

theorem transportChart_eq_of_mem_inter (c d : ChartIndex A) {z : X}
    (hc : z ∈ transportChartDomain A e c) (hd : z ∈ transportChartDomain A e d) :
    c = d := by
  apply chart_eq_of_mem_inter A c d (z := e.symm z)
  · rw [← preimage_transportChartDomain A e c]
    simpa only [Set.mem_preimage, e.apply_symm_apply] using hc
  · rw [← preimage_transportChartDomain A e d]
    simpa only [Set.mem_preimage, e.apply_symm_apply] using hd

theorem transportChart_eq_of_subset (c d : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e d) : c = d :=
  chart_eq_of_subset A c d (chartDomain_subset_of_transportSubset A e c d h)

theorem transportChartDomain_injective :
    Function.Injective (transportChartDomain A e) := by
  intro c d h
  exact transportChart_eq_of_subset A e c d (by rw [h])

theorem transportChartFamily_covers (z : X) :
    ∃ c, z ∈ transportChartDomain A e c := by
  obtain ⟨c, x, hx⟩ := chartFamily_covers A (e.symm z)
  exact ⟨c, x, (congrArg e hx).trans (e.apply_symm_apply z)⟩

theorem isQuasinet_transportChartFamily :
    AtlasTopology.IsQuasinet (transportChartFamily A e) := by
  intro z
  obtain ⟨c, hc⟩ := transportChartFamily_covers A e z
  refine ⟨{transportChartDomain A e c}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · exact Set.singleton_subset_iff.mpr ⟨c, rfl⟩
  · intro U hU
    exact (Set.mem_singleton_iff.mp hU) ▸ hc
  · rw [Set.sUnion_singleton]
    exact (isOpenEmbedding_transportChart A e c).isOpen_range.mem_nhds hc

theorem isNet_transportChartFamily : AtlasTopology.IsNet (transportChartFamily A e) := by
  refine ⟨isQuasinet_transportChartFamily A e, ?_⟩
  rintro U ⟨c, rfl⟩ V ⟨d, rfl⟩ z
  have hcd := transportChart_eq_of_mem_inter A e c d z.property.1 z.property.2
  subst d
  apply AtlasTopology.isQuasinet_of_univ_mem (τ :=
    AtlasTopology.restrictedFamily (transportChartFamily A e)
      (transportChartDomain A e c ∩ transportChartDomain A e c)) ?_ z
  refine ⟨transportChartDomain A e c, ⟨c, rfl⟩, ?_, ?_⟩
  · exact fun _ h => ⟨h, h⟩
  · ext y
    exact ⟨fun _ => y.property.1, fun _ => Set.mem_univ _⟩

/-- The bounded restriction on the original quotient algebras, with its
containment obtained by pulling back through the homeomorphism. -/
def transportRestriction (c d : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e d) :
    BoundedAlgHom K (chartAlgebra A d) (chartAlgebra A c) :=
  restriction A c d (chartDomain_subset_of_transportSubset A e c d h)

theorem transportRestriction_chart (c d : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e d)
    (x : BanachSpectrum (chartAlgebra A c)) :
    transportChart A e d
        (BanachSpectrum.comap (transportRestriction A e c d h).toBoundedRingHom x) =
      transportChart A e c x :=
  congrArg e (restriction_chart A c d _ x)

/-- Factorization holds for arbitrary normed test algebras, hence for all
presented affinoids including nonstrict ones. -/
theorem transportRestriction_universal (c d : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e d)
    {R : Type z} [NormedCommRing R] [Algebra K R]
    (φ : BoundedAlgHom K (chartAlgebra A d) R) :
    ∃! ψ : BoundedAlgHom K (chartAlgebra A c) R,
      ψ.comp (transportRestriction A e c d h) = φ :=
  restriction_universal A c d _ φ

@[simp]
theorem transportRestriction_self (c : ChartIndex A)
    (h : transportChartDomain A e c ⊆ transportChartDomain A e c) :
    transportRestriction A e c c h = BoundedAlgHom.id K (chartAlgebra A c) := rfl

theorem transportRestriction_comp (c d f : ChartIndex A)
    (hcd : transportChartDomain A e c ⊆ transportChartDomain A e d)
    (hdf : transportChartDomain A e d ⊆ transportChartDomain A e f)
    (hcf : transportChartDomain A e c ⊆ transportChartDomain A e f) :
    transportRestriction A e c f hcf =
      (transportRestriction A e c d hcd).comp (transportRestriction A e d f hdf) :=
  restriction_comp A c d f _ _ _

/-- Construct an atlas on a space homeomorphic to the actual disjoint spectra.
No atlas or analytic property of the target is supplied as input. -/
def transportAtlas [CompleteSpace K] : IndexedAffinoidAtlas.{u, w, v} K X where
  Index := ChartIndex A
  algebra := chartAlgebra A
  chart := transportChart A e
  isEmbedding_chart c := (isOpenEmbedding_transportChart A e c).isEmbedding
  chartDomain_injective := transportChartDomain_injective A e
  locallyHausdorff _ := by
    let : T2Space X := e.t2Space
    exact ⟨Set.univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := isNet_transportChartFamily A e
  restriction := transportRestriction A e
  restriction_chart := transportRestriction_chart A e
  restriction_universal c d h _ φ _ := transportRestriction_universal A e c d h φ
  restriction_id := transportRestriction_self A e
  restriction_comp := transportRestriction_comp A e

end Langlands.Analytic.DisjointAffinoidAtlas
