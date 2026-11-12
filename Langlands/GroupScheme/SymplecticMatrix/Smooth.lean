import Langlands.GroupScheme.SymplecticMatrix.Basic
import Langlands.GroupScheme.CorepresentedSmooth

/-! # Smoothness of the split symplectic group scheme

A symplectic matrix over a square-zero quotient `C ⧸ N` lifts to a symplectic matrix over `C`:
starting from an arbitrary entrywise lift `g`, the defect `ε = g J gᵀ - J` is an alternating
matrix with entries in `N`, and `(1 + U J) g` is symplectic, where `U` is the strictly upper
triangular part of `ε` for an enumeration of the indices. Hence the coordinate ring of
`SymplecticMatrix.groupScheme l R` is formally smooth; it is of finite presentation, so the
group scheme is smooth over `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Matrix

namespace Langlands.GroupScheme.SymplecticMatrix

section Lifting

variable {l : Type} [Fintype l] [DecidableEq l] {C : Type*} [CommRing C]

/-- The diagonal of `A J Aᵀ` vanishes: the standard form is alternating. -/
theorem mul_J_mul_transpose_apply_self (A : Matrix (l ⊕ l) (l ⊕ l) C) (i : l ⊕ l) :
    (A * Matrix.J l C * Aᵀ) i i = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Matrix.J,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_neg, mul_ite, mul_one,
    Finset.sum_neg_distrib, Finset.mem_univ, ite_true, neg_mul,
    Finset.sum_ite_eq']
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun a _ => by ring

/-- The strictly upper triangular part of a square matrix, for the order of the indices given by
an enumeration. -/
def strictUpper (ε : Matrix (l ⊕ l) (l ⊕ l) C) : Matrix (l ⊕ l) (l ⊕ l) C :=
  Matrix.of fun i j =>
    if Fintype.equivFin (l ⊕ l) i < Fintype.equivFin (l ⊕ l) j then ε i j else 0

omit [DecidableEq l] in
/-- An alternating matrix is its strictly upper triangular part minus the transpose of it. -/
theorem strictUpper_sub_transpose (ε : Matrix (l ⊕ l) (l ⊕ l) C) (hε : εᵀ = -ε)
    (hd : ∀ i, ε i i = 0) : strictUpper ε - (strictUpper ε)ᵀ = ε := by
  ext i j
  have hji : ε j i = -ε i j := by
    simpa using congrFun (congrFun hε i) j
  simp only [strictUpper, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy (Fintype.equivFin (l ⊕ l) i) (Fintype.equivFin (l ⊕ l) j) with h | h | h
  · simp [h, lt_asymm h]
  · have hij : i = j := (Fintype.equivFin (l ⊕ l)).injective h
    subst hij
    simp [hd]
  · simp [h, lt_asymm h, hji]

variable (N : Ideal C)

/-- A matrix is small for `N` when all its entries lie in `N`. -/
def IsSmall (A : Matrix (l ⊕ l) (l ⊕ l) C) : Prop :=
  ∀ i j, A i j ∈ N

variable {N}

omit [DecidableEq l] in
theorem IsSmall.mul_left {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A)
    (B : Matrix (l ⊕ l) (l ⊕ l) C) : IsSmall N (B * A) := fun _ j =>
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hA k j)

omit [DecidableEq l] in
theorem IsSmall.mul_right {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A)
    (B : Matrix (l ⊕ l) (l ⊕ l) C) : IsSmall N (A * B) := fun i _ =>
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hA i k)

omit [Fintype l] [DecidableEq l] in
theorem IsSmall.transpose {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A) :
    IsSmall N Aᵀ := fun i j => hA j i

omit [DecidableEq l] in
theorem IsSmall.strictUpper {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A) :
    IsSmall N (SymplecticMatrix.strictUpper A) := fun i j => by
  simp only [SymplecticMatrix.strictUpper, Matrix.of_apply]
  split_ifs
  · exact hA i j
  · exact N.zero_mem

omit [DecidableEq l] in
/-- Over a square-zero ideal, products of small matrices vanish. -/
theorem IsSmall.mul_eq_zero (hN : N ^ 2 = ⊥) {A B : Matrix (l ⊕ l) (l ⊕ l) C}
    (hA : IsSmall N A) (hB : IsSmall N B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h : A i k * B k j ∈ N ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (hA i k) (hB k j)
  rwa [hN, Ideal.mem_bot] at h

omit [Fintype l] [DecidableEq l] in
/-- A matrix reducing to zero modulo `N` is small. -/
theorem isSmall_of_map_eq_zero {A : Matrix (l ⊕ l) (l ⊕ l) C}
    (h : A.map (Ideal.Quotient.mk N) = 0) : IsSmall N A := fun i j => by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact congrFun (congrFun h i) j

omit [Fintype l] [DecidableEq l] in
/-- A small matrix reduces to zero modulo `N`. -/
theorem IsSmall.map_eq_zero {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A) :
    A.map (Ideal.Quotient.mk N) = 0 := by
  ext i j
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hA i j)

/-- Correction of an approximately symplectic matrix: if `ε = g J gᵀ - J` is small for a
square-zero ideal, then `(1 + U J) g` is symplectic for the strict upper part `U` of `ε`. -/
theorem correction_mem (hN : N ^ 2 = ⊥) (g : Matrix (l ⊕ l) (l ⊕ l) C)
    (hε : IsSmall N (g * Matrix.J l C * gᵀ - Matrix.J l C)) :
    (1 + strictUpper (g * Matrix.J l C * gᵀ - Matrix.J l C) * Matrix.J l C) * g ∈
      Matrix.symplecticGroup l C := by
  set J := Matrix.J l C with hJdef
  set ε := g * J * gᵀ - J with hεdef
  set U := strictUpper ε with hUdef
  set E := U * J with hEdef
  have hεT : εᵀ = -ε := by
    rw [hεdef, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hJdef, Matrix.J_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_neg_eq_add, neg_sub]
    abel
  have hεd : ∀ i, ε i i = 0 := fun i => by
    rw [hεdef, Matrix.sub_apply, mul_J_mul_transpose_apply_self, hJdef]
    simp [Matrix.J]
    cases i <;> simp
  have hU : IsSmall N U := hε.strictUpper
  have hE : IsSmall N E := hU.mul_right J
  have hJE : IsSmall N (J * Eᵀ) := hE.transpose.mul_left J
  have hEε : E * ε = 0 := hE.mul_eq_zero hN hε
  have hεE : ε * Eᵀ = 0 := hε.mul_eq_zero hN hE.transpose
  have hEJE : E * (J * Eᵀ) = 0 := hE.mul_eq_zero hN hJE
  have hJJ : J * J = -1 := Matrix.J_squared l C
  have hEJ : E * J = -U := by
    rw [hEdef, Matrix.mul_assoc, hJJ, Matrix.mul_neg, Matrix.mul_one]
  have hJET : J * Eᵀ = Uᵀ := by
    rw [hEdef, Matrix.transpose_mul, hJdef, Matrix.J_transpose, ← hJdef, Matrix.neg_mul,
      Matrix.mul_neg, ← Matrix.mul_assoc, hJJ, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hP : g * J * gᵀ = J + ε := by rw [hεdef, add_sub_cancel]
  rw [SymplecticGroup.mem_iff, Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_one]
  calc (1 + E) * g * J * (gᵀ * (1 + Eᵀ)) = (1 + E) * (g * J * gᵀ) * (1 + Eᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = (1 + E) * (J + ε) * (1 + Eᵀ) := by rw [hP]
    _ = J + ε + E * J + J * Eᵀ + E * ε + ε * Eᵀ + E * (J * Eᵀ) + E * ε * Eᵀ := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J := by
        rw [hEε, hεE, hEJE, Matrix.zero_mul, hEJ, hJET, add_zero, add_zero, add_zero, add_zero,
          ← strictUpper_sub_transpose ε hεT hεd]
        abel

/-- **Infinitesimal lifting.** Every symplectic matrix over a square-zero quotient `C ⧸ N` lifts
to a symplectic matrix over `C`. -/
theorem exists_map_eq (hN : N ^ 2 = ⊥) (x : Matrix.symplecticGroup l (C ⧸ N)) :
    ∃ y : Matrix.symplecticGroup l C, map l (Ideal.Quotient.mk N) y = x := by
  let g : Matrix (l ⊕ l) (l ⊕ l) C := Matrix.of fun i j =>
    Function.surjInv Ideal.Quotient.mk_surjective ((x : Matrix (l ⊕ l) (l ⊕ l) (C ⧸ N)) i j)
  have hg : g.map (Ideal.Quotient.mk N) = x := by
    ext i j
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hε : IsSmall N (g * Matrix.J l C * gᵀ - Matrix.J l C) := by
    apply isSmall_of_map_eq_zero
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hg, Matrix.map_J,
      SymplecticGroup.mem_iff.mp x.2, sub_self]
  refine ⟨⟨_, correction_mem hN g hε⟩, Subtype.ext ?_⟩
  have hE : IsSmall N (strictUpper (g * Matrix.J l C * gᵀ - Matrix.J l C) * Matrix.J l C) :=
    hε.strictUpper.mul_right _
  change ((1 + _) * g).map (Ideal.Quotient.mk N) = _
  rw [← RingHom.mapMatrix_apply, map_mul, map_add, map_one, RingHom.mapMatrix_apply,
    hE.map_eq_zero, add_zero, one_mul, RingHom.mapMatrix_apply, hg]

end Lifting

section Algebra

variable (l : Type) [Fintype l] [DecidableEq l] (R : Type u) [CommRing R]

/-- The defining ideal is finitely generated. -/
theorem ideal_fg : (ideal l R).FG :=
  Submodule.fg_span (Set.finite_range _)

instance finitePresentation_coordinateRing :
    Algebra.FinitePresentation R (CoordinateRing l R) :=
  Algebra.FinitePresentation.quotient (ideal_fg l R)

instance formallySmooth_coordinateRing : Algebra.FormallySmooth R (CoordinateRing l R) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ N hN f => ?_
  obtain ⟨y, hy⟩ := exists_map_eq hN (point f)
  refine ⟨classify y, ?_⟩
  rw [← classify_map]
  change classify (map l (Ideal.Quotient.mk N) y) = f
  rw [hy, classify_point]

instance smooth_coordinateRing : Algebra.Smooth R (CoordinateRing l R) where

end Algebra

/-- **Smoothness.** The split symplectic group scheme is smooth over its base. -/
instance smooth_groupScheme (l : Type) [Fintype l] [DecidableEq l] (R : CommRingCat.{u}) :
    Smooth (groupScheme l R).X.hom :=
  Corepresented.smooth_groupScheme_iff.mpr
    (inferInstanceAs (Algebra.Smooth R (CoordinateRing l R)))

end Langlands.GroupScheme.SymplecticMatrix
