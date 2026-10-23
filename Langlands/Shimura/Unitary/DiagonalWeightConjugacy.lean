import Langlands.Shimura.Unitary.ComplexWeightConjugacy
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

noncomputable section
open Matrix
open scoped Classical

namespace Langlands.Shimura.ComplexMatrix

variable {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]

/-- A permutation that takes the target inverse-weight support to the source support. -/
def weightSupportPermutation
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) :
    Equiv.Perm (Fin n) :=
  (Fintype.equivOfCardEq (α := {j // q j}) (β := {j // p j})
    (by simpa only [Fintype.card_subtype] using h.symm)).extendSubtype

/-- The chosen permutation matches the two inverse-weight predicates. -/
theorem weightSupportPermutation_spec
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) (j : Fin n) :
    p (weightSupportPermutation p q h j) ↔ q j := by
  let e := Fintype.equivOfCardEq (α := {j // q j}) (β := {j // p j})
    (by simpa only [Fintype.card_subtype] using h.symm)
  change p (e.extendSubtype j) ↔ q j
  by_cases hj : q j
  · exact iff_of_true (e.extendSubtype_mem j hj) hj
  · exact iff_of_false (e.extendSubtype_not_mem j hj) hj

variable (S : Type*) [CommRing S]

/-- A permutation matrix as a unit, with the inverse permutation giving its inverse. -/
def weightPermutationUnit (σ : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) S)ˣ where
  val := σ.permMatrix S
  inv := (σ⁻¹).permMatrix S
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

/-- Conjugating a diagonal matrix permutes its diagonal entries. -/
theorem weightPermutationUnit_conj_diagonal (σ : Equiv.Perm (Fin n)) (d : Fin n → S) :
    (weightPermutationUnit S σ : Matrix (Fin n) (Fin n) S) * Matrix.diagonal d *
      (↑((weightPermutationUnit S σ)⁻¹) : Matrix (Fin n) (Fin n) S) =
        Matrix.diagonal (d ∘ σ) := by
  change σ.permMatrix S * Matrix.diagonal d * (σ⁻¹).permMatrix S = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
    Equiv.Perm.inv_def, Equiv.symm_symm] using Matrix.submatrix_diagonal_equiv d σ

/-- The explicit simultaneous conjugator supplied by equal inverse-weight support sizes. -/
def diagonalWeightConjugator
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) :
    (Matrix (Fin n) (Fin n) S)ˣ :=
  weightPermutationUnit S (weightSupportPermutation p q h)

/-- One matrix unit conjugates the whole family, for every scalar unit. -/
theorem diagonalWeightConjugator_spec
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) (u : Sˣ) :
    (diagonalWeightConjugator p q S h : Matrix (Fin n) (Fin n) S) *
        Matrix.diagonal (fun j => if p j then (↑(u⁻¹) : S) else 1) *
        (↑((diagonalWeightConjugator p q S h)⁻¹) : Matrix (Fin n) (Fin n) S) =
      Matrix.diagonal (fun j => if q j then (↑(u⁻¹) : S) else 1) := by
  rw [diagonalWeightConjugator, weightPermutationUnit_conj_diagonal]
  congr 1
  funext j
  simp only [Function.comp_apply, weightSupportPermutation_spec p q h j]

/-- Simultaneous conjugacy of two inverse/trivial diagonal families by one matrix unit. -/
def DiagonalWeightConjugate : Prop :=
  ∃ g : (Matrix (Fin n) (Fin n) S)ˣ, ∀ u : Sˣ,
    (g : Matrix (Fin n) (Fin n) S) *
        Matrix.diagonal (fun j => if p j then (↑(u⁻¹) : S) else 1) *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) S) =
      Matrix.diagonal (fun j => if q j then (↑(u⁻¹) : S) else 1)

/-- Equal support cardinalities give simultaneous conjugacy over any commutative ring. -/
theorem diagonalWeightConjugate_of_card_eq
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) :
    DiagonalWeightConjugate p q S :=
  ⟨diagonalWeightConjugator p q S h, diagonalWeightConjugator_spec p q S h⟩

/-- Over a nontrivial complex algebra, support cardinality exactly classifies these families. -/
theorem diagonalWeightConjugate_iff_card_eq [Algebra ℂ S] [Nontrivial S] :
    DiagonalWeightConjugate p q S ↔
      (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  constructor
  · rintro ⟨g, hg⟩
    have hr := finrank_inverseWeightSpace_conj
      (fun u : Sˣ => Matrix.diagonal (fun j => if p j then (↑(u⁻¹) : S) else 1)) g
    have hf := funext hg
    rw [hf, finrank_inverseWeightSpace_diagonal, finrank_inverseWeightSpace_diagonal] at hr
    exact hr.symm
  · exact diagonalWeightConjugate_of_card_eq p q S

end Langlands.Shimura.ComplexMatrix
