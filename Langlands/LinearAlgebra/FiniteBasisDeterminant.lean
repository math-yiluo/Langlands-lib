import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Determinant transitions between finite bases of possibly different ranks -/

noncomputable section

universe u v w z

namespace Langlands.LinearAlgebra.FiniteBasisDeterminant

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The determinant unit of a change between two bases with the same index type. -/
def sameUnit {n : ℕ} (a b : Module.Basis (Fin n) R M) : Rˣ where
  val := (a.toMatrix b).det
  inv := (b.toMatrix a).det
  val_inv := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix,
      Module.Basis.toMatrix_self, Matrix.det_one]
  inv_val := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix,
      Module.Basis.toMatrix_self, Matrix.det_one]

@[simp]
lemma sameUnit_val {n : ℕ} (a b : Module.Basis (Fin n) R M) :
    (sameUnit a b : R) = (a.toMatrix b).det := rfl

lemma rank_eq [Nontrivial R] {n m : ℕ}
    (a : Module.Basis (Fin n) R M) (b : Module.Basis (Fin m) R M) : n = m := by
  simpa using (Module.finrank_eq_card_basis a).symm.trans
    (Module.finrank_eq_card_basis b)

/-- A commutative ring admitting two bases of unequal finite sizes is trivial. -/
lemma subsingleton_of_rank_ne {n m : ℕ}
    (a : Module.Basis (Fin n) R M) (b : Module.Basis (Fin m) R M)
    (h : n ≠ m) : Subsingleton R := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact hs
  · exact False.elim (h (rank_eq a b))

/-- The mixed transition unit. The unequal-rank branch can occur only over a
trivial ring and is represented by its unique unit. -/
def unit {n m : ℕ} (a : Module.Basis (Fin n) R M)
    (b : Module.Basis (Fin m) R M) : Rˣ :=
  if h : n = m then sameUnit (h ▸ a) b else 1

@[simp]
lemma unit_same {n : ℕ} (a b : Module.Basis (Fin n) R M) :
    unit a b = sameUnit a b := by
  unfold unit
  exact dite_eq_left rfl

@[simp]
lemma unit_self {n : ℕ} (a : Module.Basis (Fin n) R M) : unit a a = 1 := by
  apply Units.ext
  simp only [unit_same, sameUnit_val, Module.Basis.toMatrix_self, Matrix.det_one,
    Units.val_one]

lemma unit_mul {n m k : ℕ} (a : Module.Basis (Fin n) R M)
    (b : Module.Basis (Fin m) R M) (c : Module.Basis (Fin k) R M) :
    unit a b * unit b c = unit a c := by
  by_cases hab : n = m
  · subst m
    by_cases hbc : n = k
    · subst k
      apply Units.ext
      simp only [unit_same, Units.val_mul, sameUnit_val]
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]
    · let : Subsingleton R := subsingleton_of_rank_ne b c hbc
      exact Subsingleton.elim _ _
  · let : Subsingleton R := subsingleton_of_rank_ne a b hab
    exact Subsingleton.elim _ _

section Map

variable {S : Type w} [CommRing S] {N : Type z} [AddCommGroup N] [Module S N]

/-- Coordinate compatibility suffices to carry mixed transition determinants
through a ring homomorphism. -/
lemma map_unit {n m : ℕ} (f : R →+* S)
    (a : Module.Basis (Fin n) R M) (b : Module.Basis (Fin m) R M)
    (a' : Module.Basis (Fin n) S N) (b' : Module.Basis (Fin m) S N)
    (h : ∀ i j, f (a.repr (b j) i) = a'.repr (b' j) i) :
    f (unit a b : R) = (unit a' b' : S) := by
  by_cases hnm : n = m
  · subst m
    simp only [unit_same, sameUnit_val, RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    exact h i j
  · simp only [unit, dite_eq_right hnm, Units.val_one, map_one]

end Map

end Langlands.LinearAlgebra.FiniteBasisDeterminant
