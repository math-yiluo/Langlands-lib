import Langlands.Algebra.ReducedCharpoly
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Regular elements in finite-dimensional central simple algebras -/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.CentralSimple

open Matrix

private def charpolyResultant {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R :=
  (M.charpoly).resultant M.charpoly.derivative n (n - 1)

private theorem charpolyResultant_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    f (charpolyResultant M) = charpolyResultant (M.map f) := by
  unfold charpolyResultant
  rw [Matrix.charpoly_map, Polynomial.derivative_map, Polynomial.resultant_map_map]

private theorem charpolyResultant_ne_zero_iff {L : Type*} [Field L] [CharZero L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) : charpolyResultant M ≠ 0 ↔ M.charpoly.Separable := by
  have hn : M.charpoly.natDegree = n := by simp
  have hd : M.charpoly.derivative.natDegree = n - 1 := by rw [Polynomial.natDegree_derivative, hn]
  simpa only [hn, hd, charpolyResultant, separable_def, isUnit_iff_ne_zero] using
    (Polynomial.isUnit_resultant_iff_isCoprime (g := M.charpoly.derivative) M.charpoly_monic)

variable {K A : Type u} [Field K] [CharZero K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The reduced characteristic polynomial is separable at some point of any basis box
with infinitely many allowed coordinates in each direction. -/
theorem exists_separable_reducedCharpoly_in_basis_box {J : Type u} [Fintype J]
    (b : Module.Basis J K A) (S : J → Set K) (hS : ∀ j, (S j).Infinite) :
    ∃ c : J → K, (∀ j, c j ∈ S j) ∧ (reducedCharpoly K A (∑ j, c j • b j)).Separable := by
  classical
  let L := finiteGaloisSplittingField K A
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let e := finiteGaloisSplittingChart K A
  let n := reducedDegree K A
  let M : Matrix (Fin n) (Fin n) (MvPolynomial J L) := .of fun i k =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (e ((1 : L) ⊗ₜ[K] b j) i k)
  let p := charpolyResultant M
  have heval (c : J → L) : M.map (MvPolynomial.eval c) = e (∑ j, c j • ((1 : L) ⊗ₜ[K] b j)) := by
    ext i k
    simp [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  let D : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => (i.val : L)
  have hD : D.charpoly.Separable := by
    rw [show D = Matrix.diagonal (fun i : Fin n => (i.val : L)) from rfl,
      Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    exact Nat.cast_injective.comp Fin.val_injective
  have hp : p ≠ 0 := by
    let c : J → L := fun j => (b.baseChange L).repr (e.symm D) j
    have h := (b.baseChange L).sum_repr (e.symm D)
    have hM : M.map (MvPolynomial.eval c) = D := by
      rw [heval]
      have hsum : (∑ j, c j • ((1 : L) ⊗ₜ[K] b j)) = e.symm D := by
        simpa only [Module.Basis.baseChange_apply] using h
      rw [hsum, e.apply_symm_apply]
    have hval : MvPolynomial.eval c p = charpolyResultant D := by
      rw [show MvPolynomial.eval c p = charpolyResultant (M.map (MvPolynomial.eval c)) from
        charpolyResultant_map _ _, hM]
    exact fun h0 => (charpolyResultant_ne_zero_iff D).2 hD (by simpa [h0] using hval.symm)
  have hbox : ∃ x ∈ Set.pi Set.univ (fun j => algebraMap K L '' S j),
      MvPolynomial.eval x p ≠ 0 := by
    by_contra! h
    apply hp
    apply MvPolynomial.funext_set _ (fun j => (hS j).image (algebraMap K L).injective.injOn)
    simpa only [map_zero] using h
  obtain ⟨x, hx, hx'⟩ := hbox
  choose c hc hcx using fun j => hx j (Set.mem_univ j)
  refine ⟨c, hc, ?_⟩
  apply (Polynomial.separable_map (algebraMap K L)).mp
  rw [reducedCharpoly_map_chart K A e]
  apply (charpolyResultant_ne_zero_iff _).1
  have hterm (j : J) : x j • ((1 : L) ⊗ₜ[K] b j) = (1 : L) ⊗ₜ[K] (c j • b j) := by
    rw [← hcx j, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    simp [Algebra.smul_def]
  have hsum : (∑ j, x j • ((1 : L) ⊗ₜ[K] b j)) = (1 : L) ⊗ₜ[K] (∑ j, c j • b j) := by
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  rw [← hsum, ← heval]
  exact (charpolyResultant_map (MvPolynomial.eval x) M) ▸ hx'

omit [CharZero K] in
/-- The constant coefficient of the reduced characteristic polynomial is signed reduced norm. -/
theorem reducedCharpoly_coeff_zero (a : A) :
    (reducedCharpoly K A a).coeff 0 =
      (-1 : K) ^ reducedDegree K A * reducedNorm K A K (1 ⊗ₜ[K] a) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, reducedCharpoly_eval]
  have h : (0 : K) ⊗ₜ[K] (1 : A) - (1 : K) ⊗ₜ[K] a =
      ((-1 : K) ⊗ₜ[K] (1 : A)) * ((1 : K) ⊗ₜ[K] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp [TensorProduct.neg_tmul]
  rw [h, map_mul, reducedNorm_scalar]

omit [CharZero K] in
/-- Multiplication by a nonzero scalar scales the roots of the reduced characteristic polynomial. -/
theorem reducedCharpoly_smul (s : K) (hs : s ≠ 0) (a : A) :
    reducedCharpoly K A (s • a) =
      C (s ^ reducedDegree K A) * (reducedCharpoly K A a).comp (C s⁻¹ * X) := by
  let f : K[X] →ₐ[K] K[X] := aeval (C s⁻¹ * X)
  rw [comp_eq_aeval]
  change reducedCharpoly K A (s • a) = C (s ^ reducedDegree K A) * f (reducedCharpoly K A a)
  unfold reducedCharpoly
  rw [← reducedNorm_naturality K A f]
  have hf : f X = C s⁻¹ * X := aeval_X _
  simp only [map_sub, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hf, map_one]
  have hs₁ : C s * (C s⁻¹ * X) = X := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul]
  have hs₂ : (C s : K[X]) ⊗ₜ[K] a = (1 : K[X]) ⊗ₜ[K] (s • a) := by
    rw [← TensorProduct.smul_tmul]
    simp [Algebra.smul_def]
  have h : ((C s : K[X]) ⊗ₜ[K] (1 : A)) *
      ((C s⁻¹ * X) ⊗ₜ[K] (1 : A) - (1 : K[X]) ⊗ₜ[K] a) =
      X ⊗ₜ[K] (1 : A) - (1 : K[X]) ⊗ₜ[K] (s • a) := by
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      hs₁, one_mul, mul_one, one_mul, hs₂]
  rw [← h, map_mul, reducedNorm_scalar, map_pow]

omit [CharZero K] in
/-- Nonzero scalar multiplication preserves separability of a reduced characteristic polynomial. -/
theorem reducedCharpoly_separable_smul {s : K} (hs : s ≠ 0) {a : A}
    (ha : (reducedCharpoly K A a).Separable) : (reducedCharpoly K A (s • a)).Separable := by
  rw [reducedCharpoly_smul s hs]
  have hC : IsUnit (C (s ^ reducedDegree K A)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hs))
  apply Separable.unit_mul hC
  unfold Separable at ha ⊢
  rw [derivative_comp, derivative_C_mul_X]
  apply (isCoprime_mul_unit_left_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hs))) _ _).2
  exact ha.map (compRingHom (C s⁻¹ * X))

/-- Existence of a regular element in every box of independently infinite basis coordinates. -/
def ReducedCharpolyRegularBasisBoxStatement : Prop :=
  ∀ (K A : Type u) [Field K] [CharZero K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (J : Type u) [Fintype J] (b : Module.Basis J K A) (S : J → Set K),
    (∀ j, (S j).Infinite) →
      ∃ c : J → K, (∀ j, c j ∈ S j) ∧ (reducedCharpoly K A (∑ j, c j • b j)).Separable

/-- The resultant of the generic matrix detects regular elements. -/
theorem reducedCharpolyRegularBasisBox : ReducedCharpolyRegularBasisBoxStatement.{u} := by
  intro K A _ _ _ _ _ _ _ J _ b S hS
  exact exists_separable_reducedCharpoly_in_basis_box b S hS

end Langlands.CentralSimple
