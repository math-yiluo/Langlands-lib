/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.NoncommRing

/-!
# An integral commutative model of a quotient projector

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, first matrix construction.
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

private theorem charpoly_dvd_projector_polynomial
    {R : Type u} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (hM : IsIdempotentElem M) :
    M.charpoly ∣ (Polynomial.X - Polynomial.X ^ 2 : Polynomial R) ^ n := by
  classical
  let S := Matrix.scalar (Fin n) (Polynomial.X : Polynomial R)
  let N := M.map Polynomial.C
  have hN : N * N = N := (hM.map Polynomial.C.mapMatrix).eq
  have hSN : S * N = N * S :=
    (Matrix.scalar_commute _ (fun _ ↦ Commute.all _ _) N).eq
  have hprod : (S - N) * (1 - S - N) = S - S ^ 2 := by
    noncomm_ring [hN, hSN]
  have hs : S - S ^ 2 =
      Matrix.scalar (Fin n) (Polynomial.X - Polynomial.X ^ 2 : Polynomial R) := by
    simp only [S, map_sub, map_pow]
  refine ⟨(1 - S - N).det, ?_⟩
  calc
    (Polynomial.X - Polynomial.X ^ 2 : Polynomial R) ^ n =
        (Matrix.scalar (Fin n) (Polynomial.X - Polynomial.X ^ 2 : Polynomial R)).det := by
      simp [Matrix.scalar_apply]
    _ = ((S - N) * (1 - S - N)).det := by rw [hprod, hs]
    _ = M.charpoly * (1 - S - N).det := by
      rw [Matrix.det_mul]
      rfl


/-- A quotient projector is the reduction of the image of an element of an integral
commutative algebra, where that element is idempotent modulo the extended ideal.

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, from the choice
of the lifted matrix through the construction of the idempotent `ebar`.
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof: Lift the entries of `toMatrix' pbar` to a matrix `X` over `A`. Put
`f = charpoly X` and `B = A[x]/(f)`. Monicity makes `B` finite free and integral.
Cayley--Hamilton gives `ψ : B →ₐ[A] Mat_n(A)` sending the class `x` to `X`.
For any idempotent matrix `M` over any commutative ring, put `S = t*1` and
`N = C(M)` over its polynomial ring. Since `SN = NS` and `N^2 = N`, expansion
gives `(S-N)*(1-S-N) = (t-t^2)*1`. Taking determinants shows that
`charpoly M` divides `(t-t^2)^n`. Apply this to `M = toMatrix' pbar` and use
base change of the characteristic polynomial. Evaluating in `B/IB`, where
`f mod I` vanishes at the class of `x`, gives `(x-x^2)^(n+1)=0`.
Mathlib's `isIdempotentElem_one_sub_one_sub_pow_pow` therefore makes
`1-(1-x^(n+1))^(n+1)` idempotent modulo `IB`. Take this same polynomial in `x`
as `y` in `B`. Reduction of `ψ y` substitutes the idempotent matrix `M` for `x`:
both `M` and `1-M` equal each of their positive powers, so the result is `M`.
Using `n+1` ensures positive powers also for `n=0`. All steps hold for the
zero ring and `I=top`; no residue fields or nontriviality assumptions occur.
The determinant calculation and polynomial repair replace the residue-field
and Bezout arguments in the cited Stacks proof.
-/
theorem exists_integral_model_finite_free_projector
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (pbar : Module.End (A ⧸ I) (Fin n → A ⧸ I)) (hpbar : IsIdempotentElem pbar) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.IsIntegral A B ∧
      ∃ (ψ : B →ₐ[A] Matrix (Fin n) (Fin n) A) (y : B),
        IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) y) ∧
          (ψ y).map (Ideal.Quotient.mk I) = LinearMap.toMatrix' pbar := by
  classical
  let M := LinearMap.toMatrix' pbar
  have hM : IsIdempotentElem M := hpbar.map LinearMap.toMatrixAlgEquiv'.toRingHom
  choose entries hentries using fun i j ↦ Ideal.Quotient.mk_surjective (M i j)
  let X : Matrix (Fin n) (Fin n) A := entries
  have hXM : Matrix.map X (Ideal.Quotient.mk I) = M := by
    ext i j
    exact hentries i j
  let f := Matrix.charpoly X
  let B := Polynomial A ⧸ (Ideal.span {f} : Ideal (Polynomial A))
  let : Module.Finite A B := Matrix.charpoly_monic X |>.finite_adjoinRoot
  let ψ : B →ₐ[A] Matrix (Fin n) (Fin n) A :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (Polynomial.aeval X) (by
      intro z hz
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hz
      rw [map_mul, Matrix.aeval_self_charpoly, zero_mul])
  let x : B := Ideal.Quotient.mk (Ideal.span {f}) Polynomial.X
  have hψx : ψ x = X := by
    rw [show x = Ideal.Quotient.mk (Ideal.span {f}) Polynomial.X from rfl]
    dsimp only [ψ]
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact Polynomial.aeval_X X
  let J := I.map (algebraMap A B)
  let q := Ideal.Quotient.mk J
  let ρ : A ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
  let : Algebra (A ⧸ I) (B ⧸ J) := ρ.toAlgebra
  have hcomp : (algebraMap (A ⧸ I) (B ⧸ J)).comp (Ideal.Quotient.mk I) =
      q.comp (algebraMap A B) := by
    ext a
    rfl
  have hfroot : Polynomial.aeval x f = 0 := by
    have heval : Polynomial.aeval x = Ideal.Quotient.mkₐ A (Ideal.span {f}) := by
      ext
      simp only [Polynomial.aeval_X]
      rfl
    rw [heval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))
  have hfmod : Polynomial.aeval (q x) (f.map (Ideal.Quotient.mk I)) = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map hcomp f x, hfroot, map_zero]
  have hdvd : f.map (Ideal.Quotient.mk I) ∣
      (Polynomial.X - Polynomial.X ^ 2 : Polynomial (A ⧸ I)) ^ (n + 1) := by
    rw [← Matrix.charpoly_map, hXM]
    exact (charpoly_dvd_projector_polynomial n M hM).trans
      (pow_dvd_pow _ (Nat.le_succ n))
  have hnil : (q x - (q x) ^ 2) ^ (n + 1) = 0 := by
    have h := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hfmod
    simpa only [map_pow, map_sub, Polynomial.aeval_X] using h
  let y : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1)
  have hy : IsIdempotentElem (q y) := by
    simp only [y, map_sub, map_one, map_pow]
    exact isIdempotentElem_one_sub_one_sub_pow_pow (q x) (n + 1) hnil
  refine ⟨B, inferInstance, inferInstance, inferInstance, ψ, y, hy, ?_⟩
  change (Ideal.Quotient.mk I).mapMatrix (ψ y) = M
  simp only [y, map_sub, map_one, map_pow, hψx]
  change 1 - (1 - Matrix.map X (Ideal.Quotient.mk I) ^ (n + 1)) ^ (n + 1) = M
  rw [hXM, hM.pow_succ_eq, hM.one_sub.pow_succ_eq, sub_sub_cancel]

end AlgebraicGeometry
