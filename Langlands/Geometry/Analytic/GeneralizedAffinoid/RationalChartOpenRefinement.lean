import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Finite actual rational refinements of relative open covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- An actual rational chart inside a prescribed relative neighborhood, with
its bounded restriction to the target chart. -/
structure RelativeNeighborhood (d : RationalChart K A) (x : d.locus)
    (W : Set d.locus) where
  chart : RationalChart K A
  map : chart ⟶ d
  mem_nhds : (Subtype.val ⁻¹' chart.locus : Set d.locus) ∈ 𝓝 x
  subordinate : (Subtype.val ⁻¹' chart.locus : Set d.locus) ⊆ W

/-- Lift a relative neighborhood to the ambient spectrum, choose an actual
ambient rational neighborhood, and intersect it with the original chart. -/
def RelativeNeighborhood.ofNeighborhood (d : RationalChart K A) (x : d.locus)
    (W : Set d.locus) (hW : W ∈ 𝓝 x) : RelativeNeighborhood d x W := by
  apply Classical.choice
  obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype d.locus x W).mp hW
  obtain ⟨n, hn, hnV⟩ := exists_rational_neighborhood x.val V hV
  refine ⟨⟨d.inter n, interLeft d n, ?_, ?_⟩⟩
  · apply Filter.mem_of_superset
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hn)
    intro y hy
    change y.val ∈ (d.inter n).locus
    rw [locus_inter]
    exact ⟨y.property, hy⟩
  · intro y hy
    apply hsub
    apply hnV
    exact ((locus_inter d n) ▸ hy).2

/-- A finite family of actual rational restrictions subordinate to labelled
relative sets, whose relative interiors cover the entire target chart.
The label type has a universe independent of the scalar field. -/
structure FiniteOpenRefinement (d : RationalChart K A) {I : Type v}
    (U : I → Set d.locus) where
  size : ℕ
  chart : Fin size → RationalChart K A
  map : ∀ i, chart i ⟶ d
  label : Fin size → I
  subordinate : ∀ i, (Subtype.val ⁻¹' (chart i).locus : Set d.locus) ⊆ U (label i)
  interiors_cover : ∀ x : d.locus,
    ∃ i, x ∈ interior (Subtype.val ⁻¹' (chart i).locus : Set d.locus)

namespace FiniteOpenRefinement

variable {d : RationalChart K A} {I : Type v} {U : I → Set d.locus}

/-- Compactness selects finitely many of the constructed rational
neighborhoods subordinate to any relative open cover. -/
def ofOpenCover (d : RationalChart K A) (U : I → Set d.locus)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x : d.locus, ∃ i, x ∈ U i) :
    FiniteOpenRefinement d U := by
  classical
  let label : d.locus → I := fun x => (hcover x).choose
  let N : ∀ x : d.locus, RelativeNeighborhood d x (U (label x)) :=
    fun x => RelativeNeighborhood.ofNeighborhood d x (U (label x))
      ((hU (label x)).mem_nhds (hcover x).choose_spec)
  let V : d.locus → Set d.locus :=
    fun x => interior (Subtype.val ⁻¹' (N x).chart.locus : Set d.locus)
  letI : CompactSpace d.locus := d.toDomain.compactSpace_locus
  let htExists := CompactSpace.elim_nhds_subcover V
    (fun x => interior_mem_nhds.mpr (N x).mem_nhds)
  let t := htExists.choose
  have ht := htExists.choose_spec
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun i => (N (e i).val).chart,
    fun i => (N (e i).val).map, fun i => label (e i).val,
    fun i => (N (e i).val).subordinate, ?_⟩
  intro x
  have hmem : x ∈ ⋃ y ∈ t, V y := by
    rw [ht]
    trivial
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
  refine ⟨e.symm ⟨y, hy⟩, ?_⟩
  rw [e.apply_symm_apply]
  exact hxy

omit [CompleteSpace K] in
/-- The retained relative-interior cover in particular covers all base points. -/
theorem covers (c : FiniteOpenRefinement d U) :
    ∀ x ∈ d.locus, ∃ i, x ∈ (c.chart i).locus := by
  intro x hx
  obtain ⟨i, hi⟩ := c.interiors_cover ⟨x, hx⟩
  have hmem : (⟨x, hx⟩ : d.locus) ∈
      (Subtype.val ⁻¹' (c.chart i).locus : Set d.locus) := interior_subset hi
  exact ⟨i, hmem⟩

omit [CompleteSpace K] in
/-- Subordination applies to every point of each actual component locus. -/
theorem subordinate_point (c : FiniteOpenRefinement d U) (i : Fin c.size)
    (x : BanachSpectrum A) (hx : x ∈ (c.chart i).locus) :
    (⟨x, (c.map i).subset hx⟩ : d.locus) ∈ U (c.label i) :=
  c.subordinate i hx

/-- Forgetting only the rational presentations gives an actual finite
represented-domain cover with the original bounded restrictions. -/
def toFiniteCover (c : FiniteOpenRefinement d U) : Domain.FiniteCover d.toDomain where
  size := c.size
  obj i := (c.chart i).toDomain
  map i := (toDomainFunctor K A).map (c.map i)
  covers := c.covers

@[simp] theorem toFiniteCover_map_restriction (c : FiniteOpenRefinement d U)
    (i : Fin c.size) :
    (c.toFiniteCover.map i).restriction = (c.map i).restriction := rfl

/-- The sieve generated by the constructed actual chart arrows. -/
def coveringSieve (c : FiniteOpenRefinement d U) : Sieve d :=
  Sieve.ofArrows c.chart c.map

/-- Every such refinement is a covering in the published finite rational site.
Lifting finite indices keeps the covering witness in the scalar universe. -/
theorem coveringSieve_mem (c : FiniteOpenRefinement d U) :
    c.coveringSieve ∈ finiteRationalTopology K A d := by
  refine ⟨ULift.{u} (Fin c.size), inferInstance, fun i => c.chart i.down,
    fun i => c.map i.down, fun i => Sieve.ofArrows_mk c.chart c.map i.down, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := c.covers x hx
  exact ⟨⟨i⟩, hi⟩

/-- The empty chart locus admits a zero-member refinement for any label type. -/
def empty (d : RationalChart K A) (U : I → Set d.locus) (hd : d.locus = ∅) :
    FiniteOpenRefinement d U where
  size := 0
  chart := Fin.elim0
  map i := Fin.elim0 i
  label := Fin.elim0
  subordinate i := Fin.elim0 i
  interiors_cover x := by
    exact ((Set.eq_empty_iff_forall_notMem.mp hd) x.val x.property).elim

end FiniteOpenRefinement

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
