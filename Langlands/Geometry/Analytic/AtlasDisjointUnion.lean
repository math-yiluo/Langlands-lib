import Langlands.Geometry.Analytic.AtlasNonemptyCharts
import Langlands.Geometry.Analytic.AtlasTopology.DisjointUnion

/-! # Disjoint unions of arbitrary supplied affinoid atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasDisjointUnion

open Set Topology CategoryTheory
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I : Type z} {X : I → Type v} [∀ i, TopologicalSpace (X i)]
  (a : ∀ i, IndexedAffinoidAtlas.{u, v, w} K (X i))

/-- The original chart indices, tagged only by their component. -/
abbrev Index := (i : I) × (a i).Index

/-- No change of the original positive-polyradius quotient algebra. -/
def algebra (c : Index a) : PresentedAffinoidAlgebra K := (a c.fst).algebra c.snd

/-- Compose the original chart with the actual topological sigma injection. -/
def chart (c : Index a) : BanachSpectrum (algebra a c) → Sigma X :=
  Sigma.mk c.fst ∘ (a c.fst).chart c.snd

theorem range_chart (c : Index a) :
    Set.range (chart a c) = Sigma.mk c.fst '' Set.range ((a c.fst).chart c.snd) :=
  Set.range_comp _ _

theorem chart_subset_iff (i : I) (c d : (a i).Index) :
    Set.range (chart a ⟨i, c⟩) ⊆ Set.range (chart a ⟨i, d⟩) ↔
      Set.range ((a i).chart c) ⊆ Set.range ((a i).chart d) := by
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨t, ht⟩ := h ⟨y, congrArg (Sigma.mk i) hy⟩
    exact ⟨t, sigma_mk_injective ht⟩
  · rintro h _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    exact ⟨y, congrArg (Sigma.mk i) hy⟩

variable (ha : ∀ i, (a i).HasNonemptyCharts)

include ha in
/-- Containment forces equality of component tags, allowing arbitrary
containment and overlap of the original indices inside that component. -/
theorem tag_eq_of_subset (c d : Index a)
    (h : Set.range (chart a c) ⊆ Set.range (chart a d)) : c.fst = d.fst := by
  obtain ⟨x⟩ := ha c.fst c.snd
  obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
  exact (congrArg Sigma.fst hy).symm

include ha in
theorem chartDomain_injective :
    Function.Injective (fun c : Index a => Set.range (chart a c)) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ h
  have hij := tag_eq_of_subset a ha ⟨i, c⟩ ⟨j, d⟩ h.subset
  dsimp at hij
  subst j
  apply congrArg (Sigma.mk i)
  apply (a i).chartDomain_injective
  exact Subset.antisymm ((chart_subset_iff a i c d).mp h.subset)
    ((chart_subset_iff a i d c).mp h.symm.subset)

theorem chartFamily_eq :
    Set.range (fun c : Index a => Set.range (chart a c)) =
      AtlasTopology.sigmaFamily
        (fun i => Set.range (fun c => Set.range ((a i).chart c))) := by
  ext U
  constructor
  · rintro ⟨⟨i, c⟩, rfl⟩
    exact ⟨i, Set.range ((a i).chart c), ⟨c, rfl⟩, range_chart a ⟨i, c⟩⟩
  · rintro ⟨i, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨i, c⟩, range_chart a ⟨i, c⟩⟩

/-- Retain precisely the component restriction after transporting only the tag. -/
def restriction (c d : Index a)
    (h : Set.range (chart a c) ⊆ Set.range (chart a d)) :
    BoundedAlgHom K (algebra a d) (algebra a c) := by
  rcases c with ⟨i, c⟩
  rcases d with ⟨j, d⟩
  have hij := tag_eq_of_subset a ha ⟨i, c⟩ ⟨j, d⟩ h
  dsimp at hij
  subst j
  exact (a i).restriction c d ((chart_subset_iff a i c d).mp h)

@[simp]
theorem restriction_same (i : I) (c d : (a i).Index)
    (h : Set.range (chart a ⟨i, c⟩) ⊆ Set.range (chart a ⟨i, d⟩)) :
    restriction a ha ⟨i, c⟩ ⟨i, d⟩ h =
      (a i).restriction c d ((chart_subset_iff a i c d).mp h) := rfl

theorem restriction_chart (c d : Index a)
    (h : Set.range (chart a c) ⊆ Set.range (chart a d))
    (x : BanachSpectrum (algebra a c)) :
    chart a d (BanachSpectrum.comap (restriction a ha c d h).toBoundedRingHom x) =
      chart a c x := by
  rcases c with ⟨i, c⟩
  rcases d with ⟨j, d⟩
  have hij := tag_eq_of_subset a ha ⟨i, c⟩ ⟨j, d⟩ h
  dsimp at hij
  subst j
  exact congrArg (Sigma.mk i) ((a i).restriction_chart c d _ x)

/-- The original universal factorization is tested on every actual presented
affinoid, retaining empty spectra, nilpotents and arbitrary positive radii. -/
theorem restriction_universal (c d : Index a)
    (h : Set.range (chart a c) ⊆ Set.range (chart a d))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (algebra a d) R)
    (hφ : ∀ x : BanachSpectrum R,
      chart a d (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (chart a c)) :
    ∃! ψ : BoundedAlgHom K (algebra a c) R,
      ψ.comp (restriction a ha c d h) = φ := by
  rcases c with ⟨i, c⟩
  rcases d with ⟨j, d⟩
  have hij := tag_eq_of_subset a ha ⟨i, c⟩ ⟨j, d⟩ h
  dsimp at hij
  subst j
  apply (a i).restriction_universal c d _ R φ
  intro x
  obtain ⟨y, hy⟩ := hφ x
  exact ⟨y, sigma_mk_injective hy⟩

theorem restriction_id (c : Index a)
    (h : Set.range (chart a c) ⊆ Set.range (chart a c)) :
    restriction a ha c c h = BoundedAlgHom.id K (algebra a c) := by
  rcases c with ⟨i, c⟩
  exact (a i).restriction_id c _

theorem restriction_comp (c d e : Index a)
    (hcd : Set.range (chart a c) ⊆ Set.range (chart a d))
    (hde : Set.range (chart a d) ⊆ Set.range (chart a e))
    (hce : Set.range (chart a c) ⊆ Set.range (chart a e)) :
    restriction a ha c e hce =
      (restriction a ha c d hcd).comp (restriction a ha d e hde) := by
  rcases c with ⟨i, c⟩
  rcases d with ⟨j, d⟩
  rcases e with ⟨k, e⟩
  have hij := tag_eq_of_subset a ha ⟨i, c⟩ ⟨j, d⟩ hcd
  have hjk := tag_eq_of_subset a ha ⟨j, d⟩ ⟨k, e⟩ hde
  dsimp at hij hjk
  subst k
  subst j
  exact (a i).restriction_comp c d e _ _ _

/-- Construct the sigma-space atlas without assuming any output geometry. -/
def atlas : IndexedAffinoidAtlas.{u, max z v, max z w} K (Sigma X) where
  Index := Index a
  algebra := algebra a
  chart := chart a
  isEmbedding_chart c := IsEmbedding.sigmaMk.comp ((a c.fst).isEmbedding_chart c.snd)
  chartDomain_injective := chartDomain_injective a ha
  locallyHausdorff := by
    rintro ⟨i, x⟩
    obtain ⟨U, hU, hT2⟩ := (a i).locallyHausdorff x
    let : T2Space U := hT2
    exact ⟨Sigma.mk i '' U, isOpenMap_sigmaMk.image_mem_nhds hU,
      (IsEmbedding.sigmaMk.homeomorphImage U).t2Space⟩
  isNet_chartFamily := by
    rw [chartFamily_eq]
    exact AtlasTopology.IsNet.sigmaFamily (fun i => (a i).isNet_chartFamily)
  restriction := restriction a ha
  restriction_chart := restriction_chart a ha
  restriction_universal := restriction_universal a ha
  restriction_id := restriction_id a ha
  restriction_comp := restriction_comp a ha

theorem atlas_hasNonemptyCharts : (atlas a ha).HasNonemptyCharts :=
  fun c => ha c.fst c.snd

@[simp]
theorem atlas_algebra (c : Index a) : (atlas a ha).algebra c = (a c.fst).algebra c.snd :=
  rfl

@[simp]
theorem atlas_chart (c : Index a) (x : BanachSpectrum (algebra a c)) :
    (atlas a ha).chart c x = Sigma.mk c.fst ((a c.fst).chart c.snd x) := rfl

@[simp]
theorem atlas_restriction_same (i : I) (c d : (a i).Index)
    (h : Set.range ((atlas a ha).chart ⟨i, c⟩) ⊆
      Set.range ((atlas a ha).chart ⟨i, d⟩)) :
    (atlas a ha).restriction ⟨i, c⟩ ⟨i, d⟩ h =
      (a i).restriction c d ((chart_subset_iff a i c d).mp h) := rfl

/-- For arbitrary component atlases, remove only empty original charts first,
without changing the component spaces, then construct their disjoint union. -/
def nonemptyAtlas : IndexedAffinoidAtlas.{u, max z v, max z w} K (Sigma X) :=
  atlas (fun i => (a i).nonemptySubatlas)
    (fun i => (a i).nonemptySubatlas_hasNonemptyCharts)

theorem nonemptyAtlas_hasNonemptyCharts : (nonemptyAtlas a).HasNonemptyCharts :=
  atlas_hasNonemptyCharts _ _

@[simp]
theorem nonemptyAtlas_algebra (i : I) (c : (a i).nonemptySubatlas.Index) :
    (nonemptyAtlas a).algebra ⟨i, c⟩ = (a i).algebra c.val := rfl

@[simp]
theorem nonemptyAtlas_chart (i : I) (c : (a i).nonemptySubatlas.Index)
    (x : BanachSpectrum ((a i).algebra c.val)) :
    (nonemptyAtlas a).chart ⟨i, c⟩ x = Sigma.mk i ((a i).chart c.val x) := rfl

section Bundled

variable (A : I → AffinoidAtlasPresentation.{u, v, w} K)

/-- Bundle the constructed disjoint union of given nonempty-chart presentations. -/
def presentation (hA : ∀ i, (A i).atlas.HasNonemptyCharts) :
    AffinoidAtlasPresentation.{u, max z v, max z w} K where
  space := TopCat.of ((i : I) × (A i).space)
  atlas := atlas (fun i => (A i).atlas) hA

/-- Bundle the same actual disjoint space for arbitrary presentations, retaining
exactly the original nonempty charts and all their algebraic data. -/
def nonemptyPresentation : AffinoidAtlasPresentation.{u, max z v, max z w} K where
  space := TopCat.of ((i : I) × (A i).space)
  atlas := nonemptyAtlas (fun i => (A i).atlas)

end Bundled

end Langlands.Analytic.AtlasDisjointUnion
