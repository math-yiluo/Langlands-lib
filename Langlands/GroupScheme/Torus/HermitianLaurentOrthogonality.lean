import Langlands.GroupScheme.Torus.FiniteMatrixAlgebraLaurent
import Langlands.GroupScheme.Examples.SU3RootParameters

/-! # Orthogonality of distinct Hermitian Laurent weights -/

noncomputable section
universe u v
open scoped Matrix

namespace Langlands.GroupScheme.HermitianLaurent

set_option backward.isDefEq.respectTransparency false

open SU3Root

variable {A : Type u} [CommRing A] {M : Type u} [AddCommMonoid M]
  {ι : Type v} [Fintype ι]

/-- Coefficient conjugation fixes every Laurent monomial. -/
def coefficientInvolution (c : RingInvolution A) : RingInvolution (AddMonoidAlgebra A M) where
  bar := AddMonoidAlgebra.mapRingEquiv M c.bar
  involutive x := by
    ext m
    simp only [AddMonoidAlgebra.coeff_mapRingEquiv, RingInvolution.bar_bar]

@[simp] theorem coefficientInvolution_single (c : RingInvolution A) (m : M) (a : A) :
    (coefficientInvolution (M := M) c).bar (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (c.bar a) :=
  AddMonoidAlgebra.mapRingEquiv_single c.bar a m

/-- The full Gram preservation equation preserves the full vector pairing. -/
theorem pairing_mulVec (c : RingInvolution A) (J P : Matrix ι ι A)
    (hP : (P.map c.bar).transpose * J * P = J) (x y : ι → A) :
    dotProduct (fun r => c.bar ((P *ᵥ x) r)) (J *ᵥ (P *ᵥ y)) =
      dotProduct (fun r => c.bar (x r)) (J *ᵥ y) := by
  have hbar : (fun r => c.bar ((P *ᵥ x) r)) =
      P.map c.bar *ᵥ (fun r => c.bar (x r)) := by
    funext r
    exact RingHom.map_mulVec c.bar.toRingHom P x r
  rw [hbar, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hP]

/-- Two monomial vectors pair with the sum of their Laurent exponents. -/
theorem pairing_single (c : RingInvolution A) (J : Matrix ι ι A)
    (m n : M) (x y : ι → A) :
    dotProduct (fun r => (coefficientInvolution (M := M) c).bar
        (AddMonoidAlgebra.single m (x r)))
      ((J.map (AddMonoidAlgebra.single 0)) *ᵥ
        (fun r => AddMonoidAlgebra.single n (y r))) =
      AddMonoidAlgebra.single (m + n)
        (dotProduct (fun r => c.bar (x r)) (J *ᵥ y)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply,
    coefficientInvolution_single, Finset.mul_sum, AddMonoidAlgebra.single_mul_single,
    zero_add]
  calc
    _ = ∑ r, AddMonoidAlgebra.single (m + n)
        (∑ s, c.bar (x r) * (J r s * y s)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact (map_sum (AddMonoidAlgebra.singleAddHom (R := A) (m + n)) _ _).symm
    _ = _ := (map_sum (AddMonoidAlgebra.singleAddHom (R := A) (m + n)) _ _).symm

/-- If monomial eigenvectors of an actual isometry have nonopposite weights,
their entire Hermitian Gram pairing vanishes. -/
theorem pairing_eq_zero_of_eigenvectors (c : RingInvolution A) (J : Matrix ι ι A)
    (P : Matrix ι ι (AddMonoidAlgebra A M))
    (hP : (P.map (coefficientInvolution c).bar).transpose *
      J.map (AddMonoidAlgebra.single 0) * P = J.map (AddMonoidAlgebra.single 0))
    (m n : M) (hmn : m + n ≠ 0) (x y : ι → A)
    (hx : P *ᵥ (fun r => AddMonoidAlgebra.single 0 (x r)) =
      fun r => AddMonoidAlgebra.single m (x r))
    (hy : P *ᵥ (fun r => AddMonoidAlgebra.single 0 (y r)) =
      fun r => AddMonoidAlgebra.single n (y r)) :
    dotProduct (fun r => c.bar (x r)) (J *ᵥ y) = 0 := by
  classical
  have h := pairing_mulVec (coefficientInvolution c)
    (J.map (AddMonoidAlgebra.single 0)) P hP
    (fun r => AddMonoidAlgebra.single 0 (x r))
    (fun r => AddMonoidAlgebra.single 0 (y r))
  rw [hx, hy, pairing_single, pairing_single, zero_add] at h
  have hc := congrArg (fun p : AddMonoidAlgebra A M => p.coeff (m + n)) h
  simpa [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hmn, Ne.symm hmn] using hc

end Langlands.GroupScheme.HermitianLaurent
