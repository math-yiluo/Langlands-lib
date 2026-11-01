import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Finite ambient rational covers from relative rational neighborhoods -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K}

/-- A rational chart over the original ambient algebra, contained in a full
represented domain and a neighborhood of the specified point in that domain. -/
structure RationalNeighborhood (U : Domain K A) (x : U.locus) where
  chart : RationalChart K A
  map : chart.toDomain ⟶ U
  mem_nhds : (Subtype.val ⁻¹' chart.locus : Set U.locus) ∈ 𝓝 x

/-- A finite ambient rational cover, retaining the actual bounded restrictions. -/
structure FiniteRationalCover (U : Domain K A) where
  size : ℕ
  chart : Fin size → RationalChart K A
  map : ∀ i, (chart i).toDomain ⟶ U
  covers : ∀ x ∈ U.locus, ∃ i, x ∈ (chart i).locus

namespace FiniteRationalCover

variable {U : Domain K A}

/-- Forget only the rational presentation of each member of the finite cover. -/
def toFiniteCover (c : FiniteRationalCover U) : FiniteCover U where
  size := c.size
  obj i := (c.chart i).toDomain
  map := c.map
  covers := c.covers

/-- An empty domain admits the empty family of ambient rational charts. -/
def empty (U : Domain K A) (hU : U.locus = ∅) : FiniteRationalCover U where
  size := 0
  chart i := Fin.elim0 i
  map i := Fin.elim0 i
  covers x hx := by simp [hU] at hx

/-- Compactness of the represented locus makes a family of relative rational
neighborhoods finite. No injectivity of the representing spectrum is needed. -/
def ofNeighborhoods (U : Domain K A)
    (h : ∀ x : U.locus, Nonempty (RationalNeighborhood U x)) :
    FiniteRationalCover U := by
  classical
  let N : ∀ x : U.locus, RationalNeighborhood U x := fun x => Classical.choice (h x)
  let V : U.locus → Set U.locus := fun x => Subtype.val ⁻¹' (N x).chart.locus
  let htExists := CompactSpace.elim_nhds_subcover V (fun x => (N x).mem_nhds)
  let t := htExists.choose
  have ht := htExists.choose_spec
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun i => (N (e i).val).chart,
    fun i => (N (e i).val).map, ?_⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : U.locus) ∈ ⋃ y ∈ t, V y := by
    rw [ht]
    trivial
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
  refine ⟨e.symm ⟨y, hy⟩, ?_⟩
  rw [e.apply_symm_apply]
  exact hxy

end FiniteRationalCover

/-- The local rational-neighborhood construction is the analytic input still
needed to deduce the full finite rational-cover proposition by compactness. -/
theorem finiteRationalCoverStatement_of_neighborhoods
    (h : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A : PresentedAffinoidAlgebra K) (U : Domain K A) (x : U.locus),
      Nonempty (RationalNeighborhood U x)) :
    FiniteRationalCoverStatement.{u} := by
  intro K _ _ _ A U
  let c := FiniteRationalCover.ofNeighborhoods U (h K A U)
  exact ⟨c.size, c.chart, c.map, c.covers⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
