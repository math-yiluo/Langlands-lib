import Langlands.Global.RankinSelberg.ArchimedeanSchwartzTensor
import Langlands.Global.RankinSelberg.ComplexLocalEqualSquareFourier
import Langlands.Global.RankinSelberg.ComplexLocalPolynomialGaussian
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Schwartz and polynomial-Gaussian square products in equal rank -/

noncomputable section

open Langlands.Archimedean (unitaryCompact)
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {m : ℕ}

local notation "n" => m + 1
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "Line" => Matrix (Fin 1) (Fin n) ℂ
local notation "Poly[" i "]" => MvPolynomial (ComplexMatrixPolynomialIndex i n) ℂ

private def rowBlock (m : ℕ) : Bool → Type
  | true => Matrix (Fin m) (Fin (m + 1)) ℂ
  | false => Fin (m + 1) → ℂ

private instance rowBlock_normedAddCommGroup (b : Bool) : NormedAddCommGroup (rowBlock m b) := by
  cases b <;> dsimp [rowBlock] <;> infer_instance

private instance rowBlock_normedSpace (b : Bool) : NormedSpace ℝ (rowBlock m b) := by
  cases b <;> dsimp [rowBlock] <;> infer_instance

private instance rowBlock_finiteDimensional (b : Bool) : FiniteDimensional ℝ (rowBlock m b) := by
  cases b <;> dsimp [rowBlock] <;> infer_instance

private def splitRows : Mat ≃L[ℝ] ((b : Bool) → rowBlock m b) := by
  let e : Mat ≃ₗ[ℝ] ((b : Bool) → rowBlock m b) :=
    { toFun := fun X b => Bool.rec (motive := rowBlock m) (X (Fin.last m)) (complexSquareFirstRows X) b
      invFun := fun p => Fin.snoc (p true) (p false)
      left_inv := fun X => Fin.snoc_init_self X
      right_inv := by
        intro p
        funext b
        cases b
        · exact Fin.snoc_last _ _
        · funext i
          change Fin.snoc (α := fun _ : Fin n => Row) (p true) (p false) i.castSucc = p true i
          simp only [Fin.snoc_castSucc]
      map_add' := by intros; funext b; cases b <;> rfl
      map_smul' := by intros; funext b; cases b <;> rfl }
  exact e.toContinuousLinearEquiv

/-- The product of the rectangular and final-row tests as a square Schwartz function. -/
def complexSquareProductSchwartz (Φ : 𝓢(Rect, ℂ)) (φ : 𝓢(Row, ℂ)) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitRows (m := m))
    (EqualSchwartzTensor.finiteTensor (fun b =>
      Bool.rec (motive := fun b => 𝓢(rowBlock m b, ℂ)) φ Φ b))

@[simp]
theorem complexSquareProductSchwartz_apply (Φ : 𝓢(Rect, ℂ)) (φ : 𝓢(Row, ℂ)) (X : Mat) :
    complexSquareProductSchwartz Φ φ X = complexSquareProductTest Φ φ X := by
  rw [complexSquareProductSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, EqualSchwartzTensor.finiteTensor_apply, Fintype.prod_bool]
  rfl

private def rowMatrixEquiv : Row ≃L[ℝ] Line :=
  ({ toFun := fun v _ => v
     invFun := fun X => X 0
     left_inv := fun _ => rfl
     right_inv := by
       intro X
       funext i
       rw [Subsingleton.elim i 0]
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Row ≃ₗ[ℝ] Line).toContinuousLinearEquiv

/-- A polynomial Gaussian on one row, with the row identified with a one-row matrix. -/
def complexRowPolynomialGaussianSchwartz (t : ℝ) (ht : 0 < t) (p : Poly[1]) : 𝓢(Row, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowMatrixEquiv (m := m))
    (complexMatrixPolynomialGaussianSchwartz t ht p)

private def firstRowsPolynomialIndex :
    ComplexMatrixPolynomialIndex m n → ComplexMatrixPolynomialIndex n n :=
  Sum.map (fun p => (p.1.castSucc, p.2)) (fun p => (p.1.castSucc, p.2))

private def lastRowPolynomialIndex :
    ComplexMatrixPolynomialIndex 1 n → ComplexMatrixPolynomialIndex n n :=
  Sum.map (fun p => (Fin.last m, p.2)) (fun p => (Fin.last m, p.2))

private theorem squareProduct_polynomialGaussian (t : ℝ) (ht : 0 < t) (p : Poly[m]) (q : Poly[1])
    (X : Mat) :
    complexSquareProductTest (complexMatrixPolynomialGaussianSchwartz t ht p)
      (complexRowPolynomialGaussianSchwartz t ht q) X =
      complexMatrixPolynomialGaussian t
        (MvPolynomial.rename firstRowsPolynomialIndex p * MvPolynomial.rename lastRowPolynomialIndex q)
        X := by
  have hfirst : complexMatrixPolynomialCoordinates X ∘ firstRowsPolynomialIndex =
      complexMatrixPolynomialCoordinates (complexSquareFirstRows X) := by
    funext i
    cases i <;> rfl
  have hlast : complexMatrixPolynomialCoordinates X ∘ lastRowPolynomialIndex =
      complexMatrixPolynomialCoordinates (rowMatrixEquiv (X (Fin.last m))) := by
    funext i
    cases i <;> rfl
  have hnorm : (∑ i : Fin n, ∑ j : Fin n, ‖X i j‖ ^ 2) =
      (∑ i : Fin m, ∑ j : Fin n, ‖complexSquareFirstRows X i j‖ ^ 2) +
        (∑ i : Fin 1, ∑ j : Fin n, ‖rowMatrixEquiv (X (Fin.last m)) i j‖ ^ 2) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  unfold complexSquareProductTest complexRowPolynomialGaussianSchwartz
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    complexMatrixPolynomialGaussianSchwartz_apply, complexMatrixPolynomialGaussianSchwartz_apply]
  unfold complexMatrixPolynomialGaussian
  rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, hfirst, hlast]
  have hExp :
      Complex.exp (-((t * (∑ i : Fin n, ∑ j : Fin n, ‖X i j‖ ^ 2) : ℝ) : ℂ)) =
      Complex.exp (-((t * (∑ i : Fin m, ∑ j : Fin n, ‖complexSquareFirstRows X i j‖ ^ 2) : ℝ) : ℂ)) *
      Complex.exp (-((t * (∑ i : Fin 1, ∑ j : Fin n, ‖rowMatrixEquiv (X (Fin.last m)) i j‖ ^ 2) :
        ℝ) : ℂ)) := by
    rw [hnorm, mul_add, Complex.ofReal_add, neg_add, Complex.exp_add]
  change _ * Complex.exp (-((t * (∑ i : Fin m, ∑ j : Fin n,
    ‖complexSquareFirstRows X i j‖ ^ 2) : ℝ) : ℂ)) *
      (_ * Complex.exp (-((t * (∑ i : Fin 1, ∑ j : Fin n,
        ‖rowMatrixEquiv (X (Fin.last m)) i j‖ ^ 2) : ℝ) : ℂ))) =
    _ * Complex.exp (-((t * (∑ i : Fin n, ∑ j : Fin n, ‖X i j‖ ^ 2) : ℝ) : ℂ))
  rw [hExp]
  ring

/-- Polynomial-Gaussian factors of a common scale give a square Schwartz
test with finite-dimensional span under unitary left translation. -/
def ComplexLocalEqualProductSchwartzStatement : Prop :=
  ∀ (t : ℝ) (ht : 0 < t) (p : Poly[m]) (q : Poly[1]),
    let Φ := complexSquareProductSchwartz (complexMatrixPolynomialGaussianSchwartz t ht p)
      (complexRowPolynomialGaussianSchwartz t ht q)
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      fun X : Mat => Φ ((k.val⁻¹).val * X)))

theorem complexLocalEqualProductSchwartz : ComplexLocalEqualProductSchwartzStatement (m := m) := by
  intro t ht p q Φ
  let Q := MvPolynomial.rename firstRowsPolynomialIndex p * MvPolynomial.rename lastRowPolynomialIndex q
  have hΦ :
      (fun k : unitaryCompact ℂ n => fun X : Mat => Φ ((k.val⁻¹).val * X)) =
      (fun k : unitaryCompact ℂ n => fun X : Mat =>
        complexMatrixPolynomialGaussian t Q ((k.val⁻¹).val * X)) := by
    funext k X
    exact (complexSquareProductSchwartz_apply _ _ _).trans (squareProduct_polynomialGaussian t ht p q _)
  rw [hΦ]
  exact (@complexLocalPolynomialGaussian n n t Q).2.1

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
