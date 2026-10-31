import Langlands.Geometry.Analytic.AtlasTopology.Restriction
import Langlands.Geometry.Analytic.ChosenAtlasMorphisms

/-! # The supplied atlas restricted to an actual chart domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Exactly the original charts contained in the indicated original chart domain. -/
def ContainedChart (j : a.Index) :=
  {i : a.Index // Set.range (a.chart i) ⊆ Set.range (a.chart j)}

/-- The original chart regarded as a map into the actual containing subspace. -/
def containedChart (j : a.Index) (c : a.ContainedChart j) :
    BanachSpectrum (a.algebra c.val) → Set.range (a.chart j) :=
  fun x => ⟨a.chart c.val x, c.property ⟨x, rfl⟩⟩

theorem range_containedChart (j : a.Index) (c : a.ContainedChart j) :
    Set.range (a.containedChart j c) =
      (Subtype.val ⁻¹' Set.range (a.chart c.val) : Set (Set.range (a.chart j))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

theorem chart_subset_of_containedSubset (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range (a.containedChart j c) ⊆ Set.range (a.containedChart j d)) :
    Set.range (a.chart c.val) ⊆ Set.range (a.chart d.val) := by
  rw [a.range_containedChart, a.range_containedChart] at h
  intro x hx
  exact h (show (⟨x, c.property hx⟩ : Set.range (a.chart j)) ∈
    (Subtype.val ⁻¹' Set.range (a.chart c.val)) from hx)

theorem containedChart_subset (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range (a.chart c.val) ⊆ Set.range (a.chart d.val)) :
    Set.range (a.containedChart j c) ⊆ Set.range (a.containedChart j d) := by
  rw [a.range_containedChart, a.range_containedChart]
  exact Set.preimage_mono h

/-- The chart family is the whole contained-member family, not a selected subcover. -/
theorem containedChartFamily_eq (j : a.Index) :
    Set.range (fun c => Set.range (a.containedChart j c)) =
      AtlasTopology.restrictedFamily (Set.range (fun i => Set.range (a.chart i)))
        (Set.range (a.chart j)) := by
  ext U
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Set.range (a.chart c.val), ⟨c.val, rfl⟩, c.property,
      a.range_containedChart j c⟩
  · rintro ⟨_, ⟨i, rfl⟩, hij, rfl⟩
    exact ⟨⟨i, hij⟩, a.range_containedChart j ⟨i, hij⟩⟩

theorem isNet_containedChartFamily (j : a.Index) :
    AtlasTopology.IsNet (Set.range (fun c => Set.range (a.containedChart j c))) := by
  rw [a.containedChartFamily_eq]
  exact a.isNet_chartFamily.restrict_member ⟨j, rfl⟩

/-- Retain the actual original bounded restriction. -/
def containedRestriction (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range (a.containedChart j c) ⊆ Set.range (a.containedChart j d)) :
    BoundedAlgHom K (a.algebra d.val) (a.algebra c.val) :=
  a.restriction c.val d.val (a.chart_subset_of_containedSubset j c d h)

theorem containedRestriction_chart (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range (a.containedChart j c) ⊆ Set.range (a.containedChart j d))
    (x : BanachSpectrum (a.algebra c.val)) :
    a.containedChart j d
        (BanachSpectrum.comap (a.containedRestriction j c d h).toBoundedRingHom x) =
      a.containedChart j c x :=
  Subtype.ext (a.restriction_chart c.val d.val _ x)

/-- Full factorization on all presented affinoid tests descends to the actual subspace. -/
theorem containedRestriction_universal (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range (a.containedChart j c) ⊆ Set.range (a.containedChart j d))
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra d.val) R)
    (hφ : ∀ x : BanachSpectrum R,
      a.containedChart j d (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        Set.range (a.containedChart j c)) :
    ∃! ψ : BoundedAlgHom K (a.algebra c.val) R,
      ψ.comp (a.containedRestriction j c d h) = φ := by
  apply a.restriction_universal c.val d.val _ R φ
  intro x
  obtain ⟨y, hy⟩ := hφ x
  exact ⟨y, congrArg Subtype.val hy⟩

/-- Construct the atlas on a chart's actual domain, retaining all contained charts,
their original algebras, and their bounded restrictions. -/
def chartAtlas (j : a.Index) :
    IndexedAffinoidAtlas.{u, v, w} K (Set.range (a.chart j)) where
  Index := a.ContainedChart j
  algebra c := a.algebra c.val
  chart := a.containedChart j
  isEmbedding_chart c :=
    (a.isEmbedding_chart c.val).codRestrict (Set.range (a.chart j)) _
  chartDomain_injective := by
    intro c d h
    apply Subtype.ext
    apply a.chartDomain_injective
    exact Set.Subset.antisymm
      (a.chart_subset_of_containedSubset j c d h.subset)
      (a.chart_subset_of_containedSubset j d c h.symm.subset)
  locallyHausdorff _ := by
    let : T2Space (Set.range (a.chart j)) := (a.isEmbedding_chart j).toHomeomorph.t2Space
    exact ⟨Set.univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := a.isNet_containedChartFamily j
  restriction := a.containedRestriction j
  restriction_chart := a.containedRestriction_chart j
  restriction_universal := a.containedRestriction_universal j
  restriction_id c h := a.restriction_id c.val _
  restriction_comp c d e hcd hde hce := a.restriction_comp c.val d.val e.val _ _ _

@[simp]
theorem chartAtlas_algebra (j : a.Index) (c : a.ContainedChart j) :
    (a.chartAtlas j).algebra c = a.algebra c.val := rfl

@[simp]
theorem chartAtlas_chart_val (j : a.Index) (c : a.ContainedChart j)
    (x : BanachSpectrum (a.algebra c.val)) :
    ((a.chartAtlas j).chart c x).val = a.chart c.val x := rfl

@[simp]
theorem chartAtlas_restriction (j : a.Index) (c d : a.ContainedChart j)
    (h : Set.range ((a.chartAtlas j).chart c) ⊆ Set.range ((a.chartAtlas j).chart d)) :
    (a.chartAtlas j).restriction c d h =
      a.restriction c.val d.val (a.chart_subset_of_containedSubset j c d h) := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The constructed presentation on the actual subspace of an original chart. -/
def chartPresentation (j : A.atlas.Index) : AffinoidAtlasPresentation.{u, v, w} K where
  space := TopCat.of (Set.range (A.atlas.chart j))
  atlas := A.atlas.chartAtlas j

/-- Subspace inclusion, with original chart indices and bounded identity pullbacks. -/
def chartInclusion (j : A.atlas.Index) : A.chartPresentation j ⟶ A where
  baseMap := ⟨Subtype.val, continuous_subtype_val⟩
  indexMap c := c.val
  index_mono := A.atlas.chart_subset_of_containedSubset j
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Inclusion between nested chart domains, retaining all the source charts. -/
def chartMap (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    A.chartPresentation i ⟶ A.chartPresentation j where
  baseMap := ⟨Set.inclusion hij, continuous_subtype_val.subtype_mk _⟩
  indexMap c := ⟨c.val, c.property.trans hij⟩
  index_mono c d h := A.atlas.containedChart_subset j _ _
    (A.atlas.chart_subset_of_containedSubset i c d h)
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

@[simp]
theorem chartMap_id (i : A.atlas.Index)
    (hii : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i)) :
    A.chartMap i i hii = 𝟙 (A.chartPresentation i) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

theorem chartMap_comp (i j k : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j))
    (hjk : Set.range (A.atlas.chart j) ⊆ Set.range (A.atlas.chart k))
    (hik : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart k)) :
    A.chartMap i j hij ≫ A.chartMap j k hjk = A.chartMap i k hik :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem chartMap_chartInclusion (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    A.chartMap i j hij ≫ A.chartInclusion j = A.chartInclusion i :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem chartInclusion_apply (j : A.atlas.Index)
    (x : Set.range (A.atlas.chart j)) :
    (A.chartInclusion j).baseMap x = x.val := rfl

@[simp]
theorem chartMap_apply (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j))
    (x : Set.range (A.atlas.chart i)) :
    ((A.chartMap i j hij).baseMap x).val = x.val := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
