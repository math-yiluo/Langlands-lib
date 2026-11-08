import Langlands.Representation.Conductor.SphericalCentral
import Langlands.Representation.RankinSelberg.SphericalTorusRecursion
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells

/-! # Integral-weight minuscule recursion in the symmetric Laurent algebra -/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa Langlands.Unramified.MinusculeCosets
open Langlands.RankinSelberg.UnramifiedWhittaker
open scoped BigOperators

universe uF uΓ uΛ

/-- The elementary symmetric polynomial in the actual Laurent algebra. -/
def symmetricTorusElementary (m k : ℕ) :
    symmetricTorusSubalgebra (Fin m) ℂ :=
  ⟨algebraMap (MvPolynomial (Fin m) ℂ) (TorusPolynomialAlgebra (Fin m) ℂ)
      (esymm (Fin m) ℂ k), fun e => by
    rw [torusPolynomialPermutation_algebraMap, esymm_isSymmetric (Fin m) ℂ k e]⟩

@[simp] theorem symmetricTorusEvaluation_elementary
    (m k : ℕ) (x : Fin m → ℂˣ) :
    symmetricTorusEvaluation (Fin m) ℂ x (symmetricTorusElementary m k) =
      Langlands.Unramified.elementaryCoefficient
        (Langlands.Unramified.Eigenvalues.ofTuple x) k := by
  change torusPolynomialEvaluation (Fin m) ℂ x
    (algebraMap (MvPolynomial (Fin m) ℂ) (TorusPolynomialAlgebra (Fin m) ℂ)
      (esymm (Fin m) ℂ k)) = _
  rw [torusPolynomialEvaluation_algebraMap]
  exact eval_esymm_eq_elementaryCoefficient x k

/-- The normalized standard minuscule Hecke eigenvalue, as an actual
symmetric Laurent polynomial. -/
def symmetricTorusHeckeScalar (n q k : ℕ) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k))) *
      symmetricTorusElementary (n + 1) k

@[simp] theorem symmetricTorusEvaluation_heckeScalar
    (n q k : ℕ) (x : Fin (n + 1) → ℂˣ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x (symmetricTorusHeckeScalar n q k) =
      (Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple x) k := by
  simp only [symmetricTorusHeckeScalar, map_mul, AlgHom.commutes,
    symmetricTorusEvaluation_elementary, Algebra.algebraMap_self, RingHom.id_apply]

open scoped Classical in
/-- The integral-weight spherical torus value, with zero on nondominant weights. -/
def sphericalTorusLaurentPolynomial {n : ℕ} (q : ℕ) (lam : Fin (n + 1) → ℤ) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  if Antitone lam then
    algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) (halfModulus q lam) *
      symmetricTorusSchur ℂ lam
  else 0

theorem sphericalTorusLaurentPolynomial_add_const {n : ℕ}
    (q : ℕ) (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    sphericalTorusLaurentPolynomial q (fun i => lam i + t) =
      (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ ^ t :
        (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)ˣ) *
          sphericalTorusLaurentPolynomial q lam := by
  classical
  simp only [sphericalTorusLaurentPolynomial, antitone_add_const_iff]
  split_ifs
  · rw [halfModulus_add_const, symmetricTorusSchur_add_const]
    ring
  · exact (mul_zero _).symm

theorem symmetricTorusEvaluation_torusLaurent_of_nonneg {n : ℕ}
    (q : ℕ) (x : Fin (n + 1) → ℂˣ) (lam : Fin (n + 1) → ℤ)
    (hpos : ∀ i, 0 ≤ lam i) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (sphericalTorusLaurentPolynomial q lam) = sphericalTorusPolynomial q x lam := by
  classical
  by_cases hlam : Antitone lam
  · simp only [sphericalTorusLaurentPolynomial, hlam, ite_true, map_mul,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      symmetricTorusEvaluation_schur, sphericalTorusPolynomial,
      dominantJacobiTrudi]
    rw [satakeSchur_eq_eval_jacobiTrudi x lam hlam hpos]
  · simp only [sphericalTorusLaurentPolynomial, hlam, ite_false, map_zero,
      sphericalTorusPolynomial, dominantJacobiTrudi, map_zero, mul_zero]

theorem sphericalTorusLaurentPolynomial_recursion_of_nonneg {n : ℕ}
    (q : ℕ) (hq : 0 < q) (lam : Fin (n + 1) → ℤ)
    (hlam : Antitone lam) (hpos : ∀ i, 0 ≤ lam i) (k : ℕ) :
    symmetricTorusHeckeScalar n q k * sphericalTorusLaurentPolynomial q lam =
      ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
        algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
          ((q : ℂ) ^ Fintype.card (RadicalPairs S.val)) *
            sphericalTorusLaurentPolynomial q (lam + subsetExponent S.val) := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  have hp (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
      0 ≤ (lam + subsetExponent S) i := by
    have hi := hpos i
    simp only [Pi.add_apply, subsetExponent]
    split_ifs <;> omega
  simpa only [map_mul, map_sum, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, symmetricTorusEvaluation_heckeScalar,
    symmetricTorusEvaluation_torusLaurent_of_nonneg q x lam hpos,
    symmetricTorusEvaluation_torusLaurent_of_nonneg q x _ (hp _)] using
      sphericalTorusPolynomial_recursion q hq x lam hlam hpos k

/-- The minuscule recursion holds for every dominant integral weight;
there is no nonnegative-weight restriction. -/
theorem sphericalTorusLaurentPolynomial_recursion {n : ℕ}
    (q : ℕ) (hq : 0 < q) (lam : Fin (n + 1) → ℤ)
    (hlam : Antitone lam) (k : ℕ) :
    symmetricTorusHeckeScalar n q k * sphericalTorusLaurentPolynomial q lam =
      ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
        algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
          ((q : ℂ) ^ Fintype.card (RadicalPairs S.val)) *
            sphericalTorusLaurentPolynomial q (lam + subsetExponent S.val) := by
  let beta : Fin (n + 1) → ℤ := fun i => lam i - lam (Fin.last n)
  have hb : Antitone beta := fun i j hij => sub_le_sub_right (hlam hij) _
  have hp : ∀ i, 0 ≤ beta i := fun i => sub_nonneg.mpr (hlam (Fin.le_last i))
  have he : lam = fun i => beta i + lam (Fin.last n) := by
    funext i
    exact (sub_add_cancel _ _).symm
  have hes (S : Finset (Fin (n + 1))) :
      lam + subsetExponent S = fun i => (beta + subsetExponent S) i + lam (Fin.last n) := by
    funext i
    simp only [Pi.add_apply, beta]
    ring
  calc
    _ = (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ ^ lam (Fin.last n) :
          (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)ˣ) *
          (symmetricTorusHeckeScalar n q k * sphericalTorusLaurentPolynomial q beta) := by
        conv_lhs => rw [he, sphericalTorusLaurentPolynomial_add_const]
        ring
    _ = _ := by
      rw [sphericalTorusLaurentPolynomial_recursion_of_nonneg q hq beta hb hp k,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [hes S.val, sphericalTorusLaurentPolynomial_add_const]
      ring

section Minuscule

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement v ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)

theorem sphericalTorusLaurentPolynomial_eq_torus
    (hθ : IsIntegrallyTrivial v θ) (lam : Fin (n + 1) → ℤ) :
    sphericalTorusLaurentPolynomial q lam =
      sphericalWhittakerPolynomial hϖ θ q (torus ϖ lam) :=
  (sphericalWhittakerPolynomial_torus hϖ θ q hθ lam).symm

variable {Λ : Type uΛ} [Fintype Λ]

/-- The actual finite sum of the spherical polynomial over the labelled
representatives of a standard minuscule double coset. -/
def sphericalWhittakerMinusculeSum (σ : Λ → F) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  ∑ a : CosetIndex Λ (n + 1) k,
    sphericalWhittakerPolynomial hϖ θ q (g * labelledRep ϖ σ a)

/-- The actual minuscule sum has the prescribed symmetric Laurent
eigenvalue at every dominant torus element, including negative weights. -/
theorem sphericalWhittakerMinusculeSum_torus
    (hq : 0 < q) (hcard : Fintype.card Λ = q)
    (hθ : IsIntegrallyTrivial v θ) (σ : Λ → F)
    (hσ : ∀ x, σ x ∈ v.integer)
    (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) (k : ℕ) :
    sphericalWhittakerMinusculeSum hϖ θ q σ k (torus ϖ lam) =
      symmetricTorusHeckeScalar n q k *
        sphericalWhittakerPolynomial hϖ θ q (torus ϖ lam) := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  have hs := sum_eval_torus_mul_labelledRep hϖ.1.le hθ
    (sphericalWhittaker_mem hϖ q x hθ) hσ hlam k
  have hr := congrArg (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)
    (sphericalTorusLaurentPolynomial_recursion q hq lam hlam k)
  simp only [map_mul, map_sum,
    sphericalTorusLaurentPolynomial_eq_torus hϖ θ q hθ,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] at hr
  simp only [sphericalWhittakerMinusculeSum, map_sum,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial, map_mul]
  rw [hs, hcard]
  exact hr.symm

end Minuscule

end Langlands.Conductor
