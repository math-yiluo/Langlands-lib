import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Langlands.Global.ArchimedeanCartanAmbientOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Ordered coordinate coefficients for Cartan polynomial expressions -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The real dimension of the original ambient matrix space. -/
abbrev cartanCoordinateDimension : ℕ :=
  Module.finrank ℝ (ArchimedeanMatrix K n)

/-- One fixed finite real basis, consisting of vectors of the original normed matrix space. -/
def cartanCoordinateBasis :
    Module.Basis (Fin (cartanCoordinateDimension K n)) ℝ (ArchimedeanMatrix K n) :=
  Module.finBasis ℝ (ArchimedeanMatrix K n)

/-- Continuous coordinates for the fixed basis, with the original norm on the source. -/
def cartanCoordinateEquiv :
    ArchimedeanMatrix K n ≃L[ℝ] (Fin (cartanCoordinateDimension K n) → ℝ) :=
  (cartanCoordinateBasis K n).equivFunL

/-- The actual real continuous coordinate functional of the fixed basis. -/
def cartanCoordinateFunctional (j : Fin (cartanCoordinateDimension K n)) :
    ArchimedeanMatrix K n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (cartanCoordinateEquiv K n).toContinuousLinearMap

/-- Complex functions indexed by all ordered coordinate words up to the declared order. -/
abbrev CartanCoordinateCoefficients (r : ℕ) :=
  (k : Fin (r + 1)) →
    (Fin k.val → Fin (cartanCoordinateDimension K n)) → ArchimedeanMatrix K n → ℂ

/-- Extend a bounded coefficient array by zero above its declared order. -/
def cartanCoefficientExtend {r : ℕ} (a : CartanCoordinateCoefficients K n r)
    (k : ℕ) (w : Fin k → Fin (cartanCoordinateDimension K n))
    (y : ArchimedeanMatrix K n) : ℂ :=
  if h : k ≤ r then a ⟨k, Nat.lt_succ_of_le h⟩ w y else 0

omit [NumberField K] in
/-- Below the declared bound, zero extension reads the original coefficient. -/
theorem cartanCoefficientExtend_of_le {r k : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (w : Fin k → Fin (cartanCoordinateDimension K n)) (y : ArchimedeanMatrix K n)
    (h : k ≤ r) :
    cartanCoefficientExtend K n a k w y = a ⟨k, Nat.lt_succ_of_le h⟩ w y := by
  simp only [cartanCoefficientExtend, dite_eq_left h]

omit [NumberField K] in
/-- Above the declared bound, every extended coefficient is zero. -/
theorem cartanCoefficientExtend_of_lt {r k : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (w : Fin k → Fin (cartanCoordinateDimension K n)) (y : ArchimedeanMatrix K n)
    (h : r < k) :
    cartanCoefficientExtend K n a k w y = 0 := by
  simp only [cartanCoefficientExtend, dite_eq_right (Nat.not_le.mpr h)]

/-- The order-zero identity array: coefficient one at the unique empty word. -/
def cartanIdentityCoefficients : CartanCoordinateCoefficients K n 0 :=
  fun _ _ _ => 1

/-- The term obtained by prepending one field coordinate to an old derivative word.
At length zero this term is absent. -/
def cartanPrependCoefficient {r : ℕ} (a : CartanCoordinateCoefficients K n r)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n) :
    (k : ℕ) → (Fin k → Fin (cartanCoordinateDimension K n)) →
      ArchimedeanMatrix K n → ℂ
  | 0, _, _ => 0
  | k + 1, w, y =>
    cartanCoefficientExtend K n a k (fun j => w j.succ) y *
      (cartanCoordinateFunctional K n (w 0) (V y) : ℂ)

/-- Explicit coefficients for formal left directional composition.
The derivative differentiates the old coefficient only; the other term
prepends the coordinate of the field to the old derivative word. -/
def cartanLeftDirectionalCoefficients {r : ℕ} (a : CartanCoordinateCoefficients K n r)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n) :
    CartanCoordinateCoefficients K n (r + 1) :=
  fun k w y =>
    (if h : k.val ≤ r then
      fderiv ℝ (a ⟨k.val, Nat.lt_succ_of_le h⟩ w) y (V y)
    else 0) +
    cartanPrependCoefficient K n a V k.val w y

/-- The actual linear matrix field of each member of the full real Cartan basis. -/
def cartanMatrixField (i : CartanBasisIndex K n)
    (y : ArchimedeanMatrix K n) : ArchimedeanMatrix K n :=
  y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)

/-- Sum of two successive left directional compositions in every actual Cartan direction. -/
def cartanSquareSumCoefficients {r : ℕ} (a : CartanCoordinateCoefficients K n r) :
    CartanCoordinateCoefficients K n (r + 1 + 1) :=
  fun k w y => ∑ i : CartanBasisIndex K n,
    cartanLeftDirectionalCoefficients K n
      (cartanLeftDirectionalCoefficients K n a (cartanMatrixField K n i))
      (cartanMatrixField K n i) k w y

/-- Explicit recursion for the coefficient array of each Cartan iterate.
The extension avoids dependent casts between `2 * (m + 1)` and `2 * m + 1 + 1`. -/
def cartanIterateCoefficients : (m : ℕ) → CartanCoordinateCoefficients K n (2 * m)
  | 0 => cartanIdentityCoefficients K n
  | m + 1 => fun k w y =>
    cartanCoefficientExtend K n
      (cartanSquareSumCoefficients K n (cartanIterateCoefficients m)) k.val w y

/-- Actual polynomial coefficient data on the original ambient matrix space.
Every iterate is padded by zero and scaled by its polynomial coefficient.
No correctness or regularity certificate is part of this construction. -/
def cartanPolynomialCoordinateOperator (p : Polynomial ℂ) :
    Langlands.Analysis.CoordinateScalarOperator (ArchimedeanMatrix K n)
      (cartanCoordinateDimension K n) (2 * p.natDegree) where
  basis := cartanCoordinateBasis K n
  coefficient := fun k w y => p.sum fun m c =>
    c * cartanCoefficientExtend K n (cartanIterateCoefficients K n m) k.val w y

/-- All polynomial arrays use the same fixed basis. -/
theorem cartanPolynomialCoordinateOperator_basis (p : Polynomial ℂ) :
    (cartanPolynomialCoordinateOperator K n p).basis = cartanCoordinateBasis K n := rfl

/-- The zero polynomial has the zero coefficient at every word of its declared order zero. -/
@[simp]
theorem cartanPolynomialCoordinateOperator_zero_coefficient
    (k : Fin (2 * (0 : Polynomial ℂ).natDegree + 1))
    (w : Fin k.val → Fin (cartanCoordinateDimension K n)) (y : ArchimedeanMatrix K n) :
    (cartanPolynomialCoordinateOperator K n 0).coefficient k w y = 0 := by
  simp [cartanPolynomialCoordinateOperator]

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (p : Polynomial ℂ),
    Langlands.Analysis.CoordinateScalarOperator (ArchimedeanMatrix K n)
      (Module.finrank ℝ (ArchimedeanMatrix K n)) (2 * p.natDegree) :=
  @cartanPolynomialCoordinateOperator

end Langlands.Global.ArchimedeanGL
