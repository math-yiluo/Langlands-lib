import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.CharP.Algebra

/-! # Separating transcendence bases of geometrically reduced field extensions

A finitely generated field extension `K / k` that is geometrically reduced has a separating
transcendence basis: a finite transcendence basis `s` such that `K` is separable over `k(s)`.
In characteristic `0` this is Mathlib's statement for perfect fields. In characteristic `p` it
follows from Mathlib's MacLane criterion once we know that `p`-th powers of `k`-linearly
independent elements of `K` stay `k`-linearly independent, which we deduce from the reducedness
of `k̄ ⊗[k] K`.
-/

open TensorProduct

namespace Langlands.CommutativeAlgebra.GeometricallyReducedSeparatingBasis

/-- Over a field `k` of prime characteristic `p`, the `p`-th powers of a finite `k`-linearly
independent family in a nontrivial geometrically reduced `k`-algebra are `k`-linearly
independent. -/
theorem linearIndependent_pow {k A ι : Type*} [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.IsGeometricallyReduced k A] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Finite ι] {v : ι → A} (hv : LinearIndependent k v) :
    LinearIndependent k fun i => v i ^ p := by
  classical
  have := Fintype.ofFinite ι
  have hp : p.Prime := Fact.out
  have hred : IsReduced (AlgebraicClosure k ⊗[k] A) :=
    (Algebra.isGeometricallyReduced_field_iff k A).mp ‹_›
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : AlgebraicClosure k →ₐ[k] AlgebraicClosure k ⊗[k] A) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k A).injective
  have : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have : CharP (AlgebraicClosure k ⊗[k] A) p := charP_of_injective_ringHom hinj p
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) (g j)) hp.pos
  have hz : (∑ j, b j ⊗ₜ[k] v j) ^ p = 0 := by
    rw [sum_pow_char]
    have hj : ∀ j, (b j ⊗ₜ[k] v j) ^ p = (1 : AlgebraicClosure k) ⊗ₜ[k] (g j • v j ^ p) := by
      intro j
      rw [Algebra.TensorProduct.tmul_pow, hb, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [Finset.sum_congr rfl fun j _ => hj j, ← TensorProduct.tmul_sum, hg,
      TensorProduct.tmul_zero]
  have hz0 : ∑ j, b j • ((1 : AlgebraicClosure k) ⊗ₜ[k] v j) = 0 := by
    have hj : ∀ j, b j • ((1 : AlgebraicClosure k) ⊗ₜ[k] v j) = b j ⊗ₜ[k] v j := by
      intro j
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun j _ => hj j]
    exact hred.eq_zero _ ⟨p, hz⟩
  have hbi := Fintype.linearIndependent_iff.mp
    (Module.Flat.linearIndependent_one_tmul (S := AlgebraicClosure k) hv) b hz0 i
  have : algebraMap k (AlgebraicClosure k) (g i) = 0 := by
    rw [← hb i, hbi, zero_pow hp.ne_zero]
  exact (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).mp this

/-- A finitely generated geometrically reduced field extension `K / k` has a separating
transcendence basis: a finite transcendence basis `s` over `k` such that `K` is separable over
the subfield `k(s)`. -/
theorem exists_isTranscendenceBasis_and_isSeparable (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.IsGeometricallyReduced k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  · exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p
      hp.out fun s hs => linearIndependent_pow p hs

end Langlands.CommutativeAlgebra.GeometricallyReducedSeparatingBasis
