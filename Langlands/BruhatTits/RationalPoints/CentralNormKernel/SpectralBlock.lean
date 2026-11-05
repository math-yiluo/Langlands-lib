import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Polynomial.Tower

/-! # Rational block projectors and spectral norms

For a matrix `A` over a complete ultrametric field `F` and a root `μ` of its characteristic
polynomial in an algebraic closure, the idempotent polynomial in `A` projecting onto the
generalized eigenspace of the minimal polynomial of `μ` has a block determinant whose norm is a
positive power of the spectral norm of `μ`. -/

noncomputable section

open Polynomial

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

/-- If every element of a multiset `s` either satisfies `p` and has spectral norm `c`, or equals
`1`, then the spectral norm of the product of `s` is `c` to the number of elements satisfying
`p`. -/
theorem spectralNorm_multiset_prod_eq_pow_countP {L : Type*} [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] (p : L → Prop) [DecidablePred p] (c : ℝ) (s : Multiset L)
    (hp : ∀ x ∈ s, p x → spectralNorm F L x = c) (h1 : ∀ x ∈ s, ¬p x → x = 1) :
    spectralNorm F L s.prod = c ^ s.countP p := by
  induction s using Multiset.induction_on with
  | empty => simp [spectralNorm_one]
  | cons a s ih =>
    have ih' := ih (fun x hx => hp x (Multiset.mem_cons_of_mem hx))
      (fun x hx => h1 x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons, ← spectralAlgNorm_def, spectralAlgNorm_mul, spectralAlgNorm_def,
      spectralAlgNorm_def, ih', Multiset.countP_cons]
    by_cases ha : p a
    · simp only [ha, ↓reduceIte]
      rw [hp a (Multiset.mem_cons_self a s) ha, pow_succ, mul_comm]
    · simp only [ha, ↓reduceIte, add_zero]
      rw [h1 a (Multiset.mem_cons_self a s) ha, spectralNorm_one, one_mul]

/-- For a root `μ` of the characteristic polynomial of `A` in `AlgebraicClosure F`, the
idempotent polynomial in `A` projecting onto the generalized eigenspace of the minimal
polynomial of `μ` along the other primary components, and the norm of the determinant of `A`
on that block: `‖det (A π + (1 - π))‖ = spectralNorm μ ^ b` with `1 ≤ b`. -/
theorem exists_blockProjector_spectralNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n F) {μ : AlgebraicClosure F}
    (hμ : (A.charpoly.map (algebraMap F (AlgebraicClosure F))).IsRoot μ) :
    ∃ P : F[X], IsIdempotentElem (aeval A P) ∧ ∃ b : ℕ, 1 ≤ b ∧
      ‖(A * aeval A P + (1 - aeval A P)).det‖ = spectralNorm F (AlgebraicClosure F) μ ^ b := by
  classical
  set q := A.charpoly
  have hq0 : q ≠ 0 := A.charpoly_monic.ne_zero
  have hint : IsIntegral F μ := Algebra.IsIntegral.isIntegral μ
  set P₀ := minpoly F μ
  have hirr : Irreducible P₀ := minpoly.irreducible hint
  have hqμ : aeval μ q = 0 := by
    rw [← eval_map_algebraMap]
    exact hμ
  have hdvd : P₀ ∣ q := minpoly.dvd F μ hqμ
  obtain ⟨a, r, hr, hq⟩ := WfDvdMonoid.max_power_factor hq0 hirr
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero, one_mul] at hq
      exact absurd (hq ▸ hdvd) hr
    · exact h
  obtain ⟨u, w, huw⟩ := (hirr.coprime_pow_of_not_dvd a hr).symm
  -- `huw : u * P₀ ^ a + w * r = 1`
  set P : F[X] := w * r with hPdef
  refine ⟨P, ?_, ?_⟩
  · have h1 : aeval A (u * P₀ ^ a) = 1 - aeval A P := by
      rw [eq_sub_iff_add_eq, ← map_add, huw, map_one]
    have h2 : aeval A P * aeval A (u * P₀ ^ a) = 0 := by
      rw [← map_mul]
      have : P * (u * P₀ ^ a) = w * u * q := by
        rw [hq, hPdef]
        ring
      rw [this, map_mul, Matrix.aeval_self_charpoly, mul_zero]
    rw [h1, mul_sub, mul_one, sub_eq_zero] at h2
    exact h2.symm
  · set G : F[X] := X * P + (1 - P) with hGdef
    have hY : A * aeval A P + (1 - aeval A P) = aeval A G := by
      simp [hGdef]
    -- the values of `G` at the roots of the characteristic polynomial
    have hG : ∀ ν : AlgebraicClosure F, aeval ν q = 0 →
        (aeval ν P₀ = 0 ∧ aeval ν G = ν) ∨ aeval ν G = 1 := by
      intro ν hν
      have huwν := congrArg (aeval ν) huw
      simp only [map_add, map_mul, map_pow, map_one] at huwν
      by_cases h0 : aeval ν P₀ = 0
      · left
        refine ⟨h0, ?_⟩
        rw [h0, zero_pow ha.ne', mul_zero, zero_add] at huwν
        have hPν : aeval ν P = 1 := huwν
        simp [hGdef, hPν]
      · right
        rw [hq, map_mul, map_pow] at hν
        have hrν : aeval ν r = 0 :=
          (mul_eq_zero.1 hν).resolve_left (pow_ne_zero _ h0)
        simp [hGdef, hPdef, hrν]
    set AL : Matrix n n (AlgebraicClosure F) := A.map (algebraMap F (AlgebraicClosure F))
      with hALdef
    set Y := aeval A G
    set YL : Matrix n n (AlgebraicClosure F) := Y.map (algebraMap F (AlgebraicClosure F))
    have hYL : YL = aeval AL (G.map (algebraMap F (AlgebraicClosure F))) := by
      rw [aeval_map_algebraMap]
      exact
        (aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId F (AlgebraicClosure F))) A G).symm
    have hσA : ∀ ν : AlgebraicClosure F,
        ν ∈ spectrum (AlgebraicClosure F) AL ↔ aeval ν q = 0 := by
      intro ν
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hALdef, Matrix.charpoly_map, IsRoot,
        eval_map_algebraMap]
    have hσY : spectrum (AlgebraicClosure F) YL =
        (fun k => eval k (G.map (algebraMap F (AlgebraicClosure F)))) ''
          spectrum (AlgebraicClosure F) AL := by
      rw [hYL]
      exact spectrum.map_polynomial_aeval_of_nonempty AL _ ⟨μ, (hσA μ).2 hqμ⟩
    have hroots : ∀ x ∈ YL.charpoly.roots, (aeval x P₀ = 0) ∨ x = 1 := by
      intro x hx
      have hxσ : x ∈ spectrum (AlgebraicClosure F) YL :=
        Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots YL.charpoly_monic.ne_zero).1 hx)
      rw [hσY] at hxσ
      obtain ⟨ν, hν, rfl⟩ := hxσ
      simp only [eval_map_algebraMap]
      rcases hG ν ((hσA ν).1 hν) with ⟨h0, hν'⟩ | h1
      · left
        rw [hν']
        exact h0
      · right
        exact h1
    have hμY : μ ∈ YL.charpoly.roots := by
      have hGμ : aeval μ G = μ := by
        have huwμ := congrArg (aeval μ) huw
        simp only [map_add, map_mul, map_pow, map_one] at huwμ
        rw [minpoly.aeval, zero_pow ha.ne', mul_zero, zero_add] at huwμ
        have hPμ : aeval μ P = 1 := huwμ
        simp [hGdef, hPμ]
      have hμσ : μ ∈ spectrum (AlgebraicClosure F) YL := by
        rw [hσY]
        exact ⟨μ, (hσA μ).2 hqμ, by simpa using hGμ⟩
      exact (mem_roots YL.charpoly_monic.ne_zero).2 (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hμσ)
    refine ⟨YL.charpoly.roots.countP (fun x => aeval x P₀ = 0), ?_, ?_⟩
    · exact Multiset.countP_pos.2 ⟨μ, hμY, minpoly.aeval F μ⟩
    · rw [hY, ← spectralNorm_extends (L := AlgebraicClosure F), RingHom.map_det,
        RingHom.mapMatrix_apply, Matrix.det_eq_prod_roots_charpoly]
      refine spectralNorm_multiset_prod_eq_pow_countP _ _ _ ?_ ?_
      · intro x _ hx
        have hmin : P₀ = minpoly F x :=
          minpoly.eq_of_irreducible_of_monic hirr hx (minpoly.monic hint)
        rw [spectralNorm, spectralNorm, ← hmin]
      · intro x hx hx'
        exact (hroots x hx).resolve_left hx'

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
