import Langlands.Shimura.PEL.HodgeDeterminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Extracting the trace from the actual binary determinant polynomial -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R]

/-- Evaluate the two variables at `(1, X)` and take the linear coefficient. -/
def traceCoefficient (p : MvPolynomial (Fin 2) R) : R :=
  (MvPolynomial.eval₂ Polynomial.C ![1, Polynomial.X] p).coeff 1

/-- This coefficient extraction commutes with every coefficient ring homomorphism. -/
theorem traceCoefficient_map {S : Type v} [CommRing S]
    (f : R →+* S) (p : MvPolynomial (Fin 2) R) :
    traceCoefficient (MvPolynomial.map f p) = f (traceCoefficient p) := by
  have hf : (Polynomial.mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := by
    ext a
    simp
  have hx : (fun i : Fin 2 => (Polynomial.mapRingHom f) (![1, Polynomial.X] i)) =
      (![1, Polynomial.X] : Fin 2 → Polynomial S) := by
    ext i
    fin_cases i <;> simp
  have h : Polynomial.map f (MvPolynomial.eval₂ Polynomial.C ![1, Polynomial.X] p) =
      MvPolynomial.eval₂ Polynomial.C ![1, Polynomial.X] (MvPolynomial.map f p) := by
    change (Polynomial.mapRingHom f)
      (MvPolynomial.eval₂ Polynomial.C ![1, Polynomial.X] p) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂_map]
    simp only [hf, hx]
  unfold traceCoefficient
  rw [← h, Polynomial.coeff_map]

variable {M : Type v} [AddCommGroup M] [Module R M]
    {κ : Type w} [Fintype κ] [DecidableEq κ]

/-- The binary determinant for the actual endomorphisms `(1, f)` has trace coefficient
equal to the intrinsic trace of `f`, over an arbitrary commutative ring. -/
theorem traceCoefficient_polynomial (b : Module.Basis κ R M) (f : Module.End R M) :
    traceCoefficient (polynomial b ![1, f]) = LinearMap.trace R M f := by
  unfold traceCoefficient
  rw [eval₂_polynomial, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_smul, LinearMap.toMatrix_one]
  rw [Matrix.map_one, Matrix.coeff_det_one_add_X_smul_one,
    LinearMap.trace_eq_matrix_trace R b] <;> simp

end Langlands.Shimura.HodgeDeterminant
