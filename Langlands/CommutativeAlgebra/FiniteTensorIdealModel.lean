import Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Data.Set.Finite.Range

/-! # Finite coefficient models of finitely generated tensor ideals -/

noncomputable section

universe u v w z

open TensorProduct

namespace Langlands.CommutativeAlgebra.TensorIdealDescent

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

open DVRAlgebraicBaseChange (stageMap)

/-- A finite set of tensors comes from one finite-dimensional intermediate field. -/
theorem exists_finiteDimensional_finset_subset_range [Algebra.IsAlgebraic K L]
    (s : Finset (L ⊗[K] A)) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ x ∈ s, x ∈ (stageMap K L A E).range := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨E₁, h₁, hx₁⟩ :=
      DVRAlgebraicBaseChange.exists_finiteDimensional_mem_range K L A x
    obtain ⟨E₂, h₂, hs₂⟩ := ih
    refine ⟨E₁ ⊔ E₂, inferInstance, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact DVRAlgebraicBaseChange.mem_range_stageMap_of_le K L A le_sup_left hx₁
    · exact DVRAlgebraicBaseChange.mem_range_stageMap_of_le K L A le_sup_right (hs₂ y hy)

/-- Lift finitely many ideal generators along any ring homomorphism whose range contains them. -/
theorem exists_fg_ideal_map_eq_span {R : Type*} {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (s : Set S) (hs : s.Finite) (hrange : s ⊆ Set.range f) :
    ∃ J : Ideal R, J.FG ∧ J.map f = Ideal.span s := by
  obtain ⟨t, _, ht, hft⟩ := hs.exists_subset_finite_image_eq
    (s := Set.univ) (by simpa using hrange)
  exact ⟨Ideal.span t, Submodule.fg_span ht, by rw [Ideal.map_span, hft]⟩

/-- Actual ideals over one finite coefficient field whose extensions are the given ideals. -/
structure FiniteTensorIdealModel {ι : Type z} (I : ι → Ideal (L ⊗[K] A)) where
  fieldStage : IntermediateField K L
  finite : FiniteDimensional K fieldStage
  ideal : ι → Ideal (fieldStage ⊗[K] A)
  fg : ∀ i, (ideal i).FG
  map_eq : ∀ i, (ideal i).map (stageMap K L A fieldStage).toRingHom = I i

namespace FiniteTensorIdealModel

variable {K L A} {ι : Type z} [Finite ι]
variable [Algebra.IsAlgebraic K L] (I : ι → Ideal (L ⊗[K] A)) (hI : ∀ i, (I i).FG)

include hI in
/-- A finite family of finitely generated tensor ideals has a common finite coefficient model. -/
theorem nonempty : Nonempty (FiniteTensorIdealModel K L A I) := by
  classical
  let _ := Fintype.ofFinite ι
  choose s hs using hI
  let t := Finset.univ.biUnion s
  obtain ⟨E, hE, ht⟩ := exists_finiteDimensional_finset_subset_range K L A t
  have hi (i : ι) :
      ∃ J : Ideal (E ⊗[K] A), J.FG ∧ J.map (stageMap K L A E).toRingHom = I i := by
    rw [← hs i]
    apply exists_fg_ideal_map_eq_span (stageMap K L A E).toRingHom _ (s i).finite_toSet
    intro x hx
    apply (AlgHom.mem_range _).mp
    exact ht x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  choose J hfg hmap using hi
  exact ⟨⟨E, hE, J, hfg, hmap⟩⟩

/-- Choose the proved common finite coefficient model. -/
def construct : FiniteTensorIdealModel K L A I :=
  Classical.choice (nonempty I hI)

end FiniteTensorIdealModel

end Langlands.CommutativeAlgebra.TensorIdealDescent
