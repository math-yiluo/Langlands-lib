import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalNeighborhoodCover

/-! # Finite ambient rational covers from finite-union neighborhoods -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K}

/-- A finite family of ambient rational charts contained in a domain whose
union is a relative neighborhood of the specified point. Individual members
need not be neighborhoods of that point. -/
structure FiniteRationalNeighborhood (U : Domain K A) (x : U.locus) where
  size : ℕ
  chart : Fin size → RationalChart K A
  map : ∀ i, (chart i).toDomain ⟶ U
  mem_nhds : (Subtype.val ⁻¹' ⋃ i, (chart i).locus : Set U.locus) ∈ 𝓝 x

namespace FiniteRationalNeighborhood

variable {U : Domain K A} {x : U.locus}

/-- A single relative rational neighborhood is a one-member family. -/
def single (N : RationalNeighborhood U x) : FiniteRationalNeighborhood U x where
  size := 1
  chart _ := N.chart
  map _ := N.map
  mem_nhds := by simpa only [Set.iUnion_const] using N.mem_nhds

/-- Pull back a neighborhood along a continuous map when its preimage is
represented by a finite union of contained ambient rational charts. -/
def ofPreimage {Y : Type v} [TopologicalSpace Y]
    (f : U.locus → Y) (hf : Continuous f) (W : Set Y) (hW : W ∈ 𝓝 (f x))
    (n : ℕ) (D : Fin n → RationalChart K A) (maps : ∀ i, (D i).toDomain ⟶ U)
    (hpreimage : f ⁻¹' W = (Subtype.val ⁻¹' ⋃ i, (D i).locus : Set U.locus)) :
    FiniteRationalNeighborhood U x where
  size := n
  chart := D
  map := maps
  mem_nhds := by
    rw [← hpreimage]
    exact hf.continuousAt.preimage_mem_nhds hW

end FiniteRationalNeighborhood

namespace FiniteRationalCover

/-- Select finitely many finite-union neighborhoods by compactness and flatten
all their chart families. This retains each actual bounded restriction. -/
def ofFiniteNeighborhoods (U : Domain K A)
    (h : ∀ x : U.locus, Nonempty (FiniteRationalNeighborhood U x)) :
    FiniteRationalCover U := by
  classical
  let N : ∀ x : U.locus, FiniteRationalNeighborhood U x :=
    fun x => Classical.choice (h x)
  let V : U.locus → Set U.locus :=
    fun x => Subtype.val ⁻¹' ⋃ i, ((N x).chart i).locus
  let htExists := CompactSpace.elim_nhds_subcover V (fun x => (N x).mem_nhds)
  let t := htExists.choose
  have ht := htExists.choose_spec
  let I := (y : t) × Fin (N y.val).size
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,
    fun i => (N (e i).1.val).chart (e i).2,
    fun i => (N (e i).1.val).map (e i).2, ?_⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : U.locus) ∈ ⋃ y ∈ t, V y := by
    rw [ht]
    trivial
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxy
  refine ⟨e.symm ⟨⟨y, hy⟩, i⟩, ?_⟩
  rw [e.apply_symm_apply]
  exact hi

end FiniteRationalCover

/-- Finite-union local rational neighborhoods suffice for the full finite
ambient rational-cover proposition, without a single-chart local hypothesis. -/
theorem finiteRationalCoverStatement_of_finiteNeighborhoods
    (h : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A : PresentedAffinoidAlgebra K) (U : Domain K A) (x : U.locus),
      Nonempty (FiniteRationalNeighborhood U x)) :
    FiniteRationalCoverStatement.{u} := by
  intro K _ _ _ A U
  let c := FiniteRationalCover.ofFiniteNeighborhoods U (h K A U)
  exact ⟨c.size, c.chart, c.map, c.covers⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
