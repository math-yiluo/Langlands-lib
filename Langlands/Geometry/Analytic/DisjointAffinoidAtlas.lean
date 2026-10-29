import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.Spectrum.Properties
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties

/-! # Concrete disjoint affinoid atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set Topology
open scoped Topology

/-- An indexed form of an affinoid atlas, using actual finite positive-polyradius
quotient algebras. The indices map bijectively onto the net of chart domains.
Domain factorization is tested on all presented affinoids, including nonstrict
ones. The bounded restriction identities are explicit algebra identities. -/
structure IndexedAffinoidAtlas (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (X : Type v) [TopologicalSpace X] where
  Index : Type w
  algebra : Index → PresentedAffinoidAlgebra K
  chart : (i : Index) → BanachSpectrum (algebra i) → X
  isEmbedding_chart : ∀ i, IsEmbedding (chart i)
  chartDomain_injective : Function.Injective (fun i => Set.range (chart i))
  locallyHausdorff : ∀ x : X, ∃ U : Set X, U ∈ 𝓝 x ∧ T2Space U
  isNet_chartFamily : AtlasTopology.IsNet (Set.range (fun i => Set.range (chart i)))
  restriction : ∀ i j, Set.range (chart i) ⊆ Set.range (chart j) →
    BoundedAlgHom K (algebra j) (algebra i)
  restriction_chart : ∀ i j h (x : BanachSpectrum (algebra i)),
    chart j (BanachSpectrum.comap (restriction i j h).toBoundedRingHom x) = chart i x
  restriction_universal : ∀ i j h (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (algebra j) R),
    (∀ x : BanachSpectrum R,
      chart j (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (chart i)) →
    ∃! ψ : BoundedAlgHom K (algebra i) R, ψ.comp (restriction i j h) = φ
  restriction_id : ∀ i h, restriction i i h = BoundedAlgHom.id K (algebra i)
  restriction_comp : ∀ i j k hij hjk hik,
    restriction i k hik = (restriction i j hij).comp (restriction j k hjk)

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The chart image of a bounded restriction is exactly the contained domain,
expressed in the containing chart's spectrum coordinates. -/
theorem range_restriction (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    Set.range (BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom) =
      a.chart j ⁻¹' Set.range (a.chart i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (a.restriction_chart i j h x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (a.isEmbedding_chart j).injective ?_⟩
    exact (a.restriction_chart i j h x).trans hx

theorem isClosed_relativeDomain (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    IsClosed (a.chart j ⁻¹' Set.range (a.chart i)) := by
  rw [← a.range_restriction i j h]
  exact (isCompact_range
    (BanachSpectrum.comapContinuous (a.restriction i j h).toBoundedRingHom).continuous).isClosed

theorem isCompactFamily_chartFamily :
    AtlasTopology.IsCompactFamily (Set.range (fun i => Set.range (a.chart i))) := by
  rintro U ⟨i, rfl⟩
  exact ⟨isCompact_range (a.isEmbedding_chart i).continuous,
    (a.isEmbedding_chart i).toHomeomorph.t2Space⟩

end IndexedAffinoidAtlas

namespace DisjointAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {I : Type v} (A : I → PresentedAffinoidAlgebra K)

/-- The actual topological disjoint union of the actual quotient spectra. -/
abbrev Space := (i : I) × BanachSpectrum (A i)

/-- Empty spectra contribute no chart to the net. This is a subtype of the
given index type, not a nonemptiness hypothesis on the family. -/
def ChartIndex := {i : I // Nonempty (BanachSpectrum (A i))}

/-- The original algebra of the indicated nonempty component. -/
def chartAlgebra (c : ChartIndex A) : PresentedAffinoidAlgebra K := A c.val

/-- Inclusion of an actual component spectrum into the disjoint union. -/
def chart (c : ChartIndex A) : BanachSpectrum (chartAlgebra A c) → Space A :=
  fun x => ⟨c.val, x⟩

def chartDomain (c : ChartIndex A) : Set (Space A) := Set.range (chart A c)

def chartFamily : Set (Set (Space A)) := Set.range (chartDomain A)

theorem isOpenEmbedding_chart (c : ChartIndex A) : IsOpenEmbedding (chart A c) :=
  IsOpenEmbedding.sigmaMk (σ := fun i => BanachSpectrum (A i)) (i := c.val)

theorem isClopen_chartDomain (c : ChartIndex A) : IsClopen (chartDomain A c) :=
  ⟨isClosed_range_sigmaMk, isOpen_range_sigmaMk⟩

/-- The homeomorphism uses the actual subspace topology on the chart domain. -/
def chartHomeomorph (c : ChartIndex A) :
    BanachSpectrum (chartAlgebra A c) ≃ₜ chartDomain A c :=
  (isOpenEmbedding_chart A c).isEmbedding.toHomeomorph

theorem chartDomain_eq_fiber (c : ChartIndex A) :
    chartDomain A c = {z : Space A | z.fst = c.val} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · rcases z with ⟨i, x⟩
    intro hi
    change i = c.val at hi
    subst i
    exact ⟨x, rfl⟩

theorem chart_eq_of_mem_inter (c d : ChartIndex A) {z : Space A}
    (hc : z ∈ chartDomain A c) (hd : z ∈ chartDomain A d) : c = d := by
  apply Subtype.ext
  rw [chartDomain_eq_fiber] at hc hd
  exact hc.symm.trans hd

/-- Nonempty chart domains cannot be properly contained in another component. -/
theorem chart_eq_of_subset (c d : ChartIndex A)
    (h : chartDomain A c ⊆ chartDomain A d) : c = d := by
  obtain ⟨x⟩ := c.property
  exact chart_eq_of_mem_inter A c d ⟨x, rfl⟩ (h ⟨x, rfl⟩)

theorem chartDomain_injective : Function.Injective (chartDomain A) := by
  intro c d h
  exact chart_eq_of_subset A c d (by rw [h])

theorem chartFamily_covers (z : Space A) : ∃ c, z ∈ chartDomain A c :=
  ⟨⟨z.fst, ⟨z.snd⟩⟩, z.snd, rfl⟩

theorem isQuasinet_chartFamily : AtlasTopology.IsQuasinet (chartFamily A) := by
  intro z
  obtain ⟨c, hc⟩ := chartFamily_covers A z
  refine ⟨{chartDomain A c}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · exact Set.singleton_subset_iff.mpr ⟨c, rfl⟩
  · intro U hU
    exact (Set.mem_singleton_iff.mp hU) ▸ hc
  · rw [Set.sUnion_singleton]
    exact (isClopen_chartDomain A c).isOpen.mem_nhds hc

theorem isNet_chartFamily : AtlasTopology.IsNet (chartFamily A) := by
  refine ⟨isQuasinet_chartFamily A, ?_⟩
  rintro U ⟨c, rfl⟩ V ⟨d, rfl⟩ z
  have hcd := chart_eq_of_mem_inter A c d z.property.1 z.property.2
  subst d
  apply AtlasTopology.isQuasinet_of_univ_mem (τ :=
    AtlasTopology.restrictedFamily (chartFamily A) (chartDomain A c ∩ chartDomain A c)) ?_ z
  refine ⟨chartDomain A c, ⟨c, rfl⟩, ?_, ?_⟩
  · exact fun _ h => ⟨h, h⟩
  · ext y
    exact ⟨fun _ => y.property.1, fun _ => Set.mem_univ _⟩

theorem isCompactFamily_chartFamily : AtlasTopology.IsCompactFamily (chartFamily A) := by
  rintro U ⟨c, rfl⟩
  exact ⟨isCompact_range (isOpenEmbedding_chart A c).continuous, inferInstance⟩

instance : LocallyCompactSpace (Space A) :=
  (isQuasinet_chartFamily A).locallyCompactSpace
    fun U hU => (isCompactFamily_chartFamily A U hU).1

/-- The chart restriction is an actual bounded identity, transported only
along the equality forced by containment of the nonempty components. -/
def restriction (c d : ChartIndex A) (h : chartDomain A c ⊆ chartDomain A d) :
    BoundedAlgHom K (chartAlgebra A d) (chartAlgebra A c) := by
  have hcd := chart_eq_of_subset A c d h
  subst d
  exact BoundedAlgHom.id K (chartAlgebra A c)

@[simp]
theorem restriction_self (c : ChartIndex A) (h : chartDomain A c ⊆ chartDomain A c) :
    restriction A c c h = BoundedAlgHom.id K (chartAlgebra A c) := rfl

theorem restriction_chart (c d : ChartIndex A)
    (h : chartDomain A c ⊆ chartDomain A d)
    (x : BanachSpectrum (chartAlgebra A c)) :
    chart A d (BanachSpectrum.comap (restriction A c d h).toBoundedRingHom x) =
      chart A c x := by
  have hcd := chart_eq_of_subset A c d h
  subst d
  rfl

/-- The factorization is proved for every normed K-algebra, so in particular
it includes every finite positive-polyradius affinoid test algebra. -/
theorem restriction_universal (c d : ChartIndex A)
    (h : chartDomain A c ⊆ chartDomain A d)
    {R : Type z} [NormedCommRing R] [Algebra K R]
    (φ : BoundedAlgHom K (chartAlgebra A d) R) :
    ∃! ψ : BoundedAlgHom K (chartAlgebra A c) R,
      ψ.comp (restriction A c d h) = φ := by
  have hcd := chart_eq_of_subset A c d h
  subst d
  refine ⟨φ, BoundedAlgHom.ext fun _ => rfl, ?_⟩
  intro ψ hψ
  exact (BoundedAlgHom.ext fun _ => rfl : ψ = ψ.comp (restriction A c c h)).trans hψ

theorem restriction_comp (c d e : ChartIndex A)
    (hcd : chartDomain A c ⊆ chartDomain A d)
    (hde : chartDomain A d ⊆ chartDomain A e)
    (hce : chartDomain A c ⊆ chartDomain A e) :
    restriction A c e hce = (restriction A c d hcd).comp (restriction A d e hde) := by
  have h₁ := chart_eq_of_subset A c d hcd
  have h₂ := chart_eq_of_subset A d e hde
  subst e
  subst d
  exact BoundedAlgHom.ext fun _ => rfl

/-- The constructed disjoint affinoid atlas. No geometry or factorization
property of the resulting space is supplied as input. -/
def atlas [CompleteSpace K] : IndexedAffinoidAtlas.{u, max u v, v} K (Space A) where
  Index := ChartIndex A
  algebra := chartAlgebra A
  chart := chart A
  isEmbedding_chart c := (isOpenEmbedding_chart A c).isEmbedding
  chartDomain_injective := chartDomain_injective A
  locallyHausdorff _ := ⟨Set.univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := isNet_chartFamily A
  restriction := restriction A
  restriction_chart := restriction_chart A
  restriction_universal c d h _ φ _ := restriction_universal A c d h φ
  restriction_id := restriction_self A
  restriction_comp := restriction_comp A

end DisjointAffinoidAtlas

end Langlands.Analytic
