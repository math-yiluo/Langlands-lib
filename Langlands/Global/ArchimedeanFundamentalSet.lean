import Langlands.Global.Adelic
import Langlands.Global.ArchimedeanGL

noncomputable section

universe u

namespace Langlands.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable (K : Type u) [Field K]

@[simp]
theorem infiniteAdeleHomeomorph_apply (x : InfiniteAdeles K) :
    infiniteAdeleHomeomorph K x =
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

@[simp]
theorem infiniteAdeleHomeomorph_symm_apply (x : NumberField.mixedEmbedding.mixedSpace K) :
    (infiniteAdeleHomeomorph K).symm x =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x := rfl

variable [NumberField K]

/-- A compact set of representatives for infinite adeles modulo algebraic integers. -/
def archimedeanFundamentalSet : Set (InfiniteAdeles K) :=
  (infiniteAdeleHomeomorph K).symm ''
    _root_.parallelepiped (NumberField.mixedEmbedding.latticeBasis K)

theorem isCompact_archimedeanFundamentalSet :
    IsCompact (archimedeanFundamentalSet K) := by
  exact (NumberField.mixedEmbedding.latticeBasis K).parallelepiped.isCompact.image
    (infiniteAdeleHomeomorph K).symm.continuous

/-- Translation by an algebraic integer moves any infinite adele into the compact set. -/
theorem exists_sub_integer_mem_archimedeanFundamentalSet (x : InfiniteAdeles K) :
    ∃ a : NumberField.RingOfIntegers K,
      x - algebraMap K (InfiniteAdeles K) (a : K) ∈ archimedeanFundamentalSet K := by
  classical
  let e := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
  obtain ⟨v, hv, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    (NumberField.mixedEmbedding.latticeBasis K) (e x)
  have hvint : (v : NumberField.mixedEmbedding.mixedSpace K) ∈
      NumberField.mixedEmbedding.integerLattice K :=
    (NumberField.mixedEmbedding.mem_span_latticeBasis K).mp v.property
  obtain ⟨a, ha⟩ := hvint
  refine ⟨-a, ?_⟩
  refine ⟨v +ᵥ e x, ZSpan.fundamentalDomain_subset_parallelepiped _ hv, ?_⟩
  change e.symm ((v : NumberField.mixedEmbedding.mixedSpace K) + e x) =
    x - algebraMap K (InfiniteAdeles K) ((-a : NumberField.RingOfIntegers K) : K)
  apply e.injective
  rw [e.apply_symm_apply, map_sub]
  change (v : NumberField.mixedEmbedding.mixedSpace K) + e x =
    e x - e (algebraMap K (InfiniteAdeles K) ((-a : NumberField.RingOfIntegers K) : K))
  rw [← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  change (v : NumberField.mixedEmbedding.mixedSpace K) + e x =
    e x - NumberField.mixedEmbedding K (-(a : K))
  rw [map_neg, sub_neg_eq_add, add_comm]
  exact congrArg (e x + ·) ha.symm

end Langlands.Global
