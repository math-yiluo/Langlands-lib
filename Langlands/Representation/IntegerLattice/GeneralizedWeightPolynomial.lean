import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock
import Langlands.LinearAlgebra.UnipotentBinomialProof
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Polynomial matrices and coefficient witnesses for actual generalized-weight blocks -/

set_option autoImplicit false

noncomputable section

namespace Langlands.IntegerLattice

universe u

/-- The factorial-normalized descending Pochhammer polynomial in coordinate `i`. -/
def coordinateBinomialPolynomial {d : ℕ} (i : Fin d) (k : ℕ) :
    MvPolynomial (Fin d) ℂ :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i)
    ((k.factorial : ℂ)⁻¹ • descPochhammer ℂ k)

/-- This coordinate polynomial evaluates to the generalized binomial coefficient
at every complex point, including every integer point of either sign. -/
@[simp] theorem eval_coordinateBinomialPolynomial {d : ℕ} (i : Fin d) (k : ℕ)
    (x : Fin d → ℂ) :
    MvPolynomial.eval x (coordinateBinomialPolynomial i k) = Ring.choose (x i) k := by
  rw [coordinateBinomialPolynomial, Polynomial.hom_eval₂]
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hcomp, Polynomial.eval₂_id]
  simpa using Langlands.complexBinomialCoefficientPolynomial k (x i)

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- One polynomial matrix factor: the finite binomial series of the actual
normalized generator difference, in a basis of its actual block. -/
def generalizedWeightBinomialMatrixFactor (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c)) (t : Fin d) :
    Matrix (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      (MvPolynomial (Fin d) ℂ) :=
  fun p q => ∑ k ∈ Finset.range (Module.finrank ℂ V),
    coordinateBinomialPolynomial t k *
      MvPolynomial.C (b.repr ((normalizedGeneratorDifference A c t ^ k) (b q)) p)

/-- The ordered product of all coordinate binomial matrix factors on the actual
block. The truncation bound in every factor is the ambient complex dimension. -/
def generalizedWeightPolynomialMatrix (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c)) :
    Matrix (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      (MvPolynomial (Fin d) ℂ) :=
  (List.ofFn (generalizedWeightBinomialMatrixFactor A c b)).prod

/-- The polynomial contribution of one actual block to a matrix coefficient,
formed from its local basis and the coordinates in an ambient block-indexed
basis. Compatibility of the two bases is a separate assertion. -/
def generalizedWeightCoefficientPolynomial (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c))
    (B : Module.Basis
      (Σ a : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A a))) ℂ V)
    (v : V) (ell : V →ₗ[ℂ] ℂ) : MvPolynomial (Fin d) ℂ :=
  ∑ p : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
    ∑ q : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
      MvPolynomial.C (ell (b p : V) * B.repr v ⟨c, q⟩) *
        generalizedWeightPolynomialMatrix A c b p q

/-- Evaluation of a single polynomial factor is the finite scalar binomial
sum of the actual normalized generator's matrix entries. -/
theorem eval_generalizedWeightBinomialMatrixFactor
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c))
    (t : Fin d) (x : Fin d → ℂ)
    (p q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))) :
    MvPolynomial.eval x (generalizedWeightBinomialMatrixFactor A c b t p q) =
      ∑ k ∈ Finset.range (Module.finrank ℂ V),
        Ring.choose (x t) k *
          b.repr ((normalizedGeneratorDifference A c t ^ k) (b q)) p := by
  simp [generalizedWeightBinomialMatrixFactor, map_sum]

/-- No factors occur at lattice rank zero, so the polynomial matrix is the identity. -/
@[simp] theorem generalizedWeightPolynomialMatrix_rank_zero
    (A : CommutingInvertibleTuple 0 V) (c : Fin 0 → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c)) :
    generalizedWeightPolynomialMatrix A c b = 1 := by
  simp [generalizedWeightPolynomialMatrix]

/-- A block of dimension zero contributes the zero coefficient polynomial. -/
theorem generalizedWeightCoefficientPolynomial_eq_zero_of_finrank_eq_zero
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c))
    (B : Module.Basis
      (Σ a : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A a))) ℂ V)
    (v : V) (ell : V →ₗ[ℂ] ℂ)
    (h : Module.finrank ℂ (generalizedWeightBlock A c) = 0) :
    generalizedWeightCoefficientPolynomial A c b B v ell = 0 := by
  have : IsEmpty (Fin (Module.finrank ℂ (generalizedWeightBlock A c))) := by
    rw [h]
    infer_instance
  simp [generalizedWeightCoefficientPolynomial]

end Langlands.IntegerLattice
