import Langlands.Shimura.Unitary.FiniteScalarExtension
import Langlands.Shimura.Unitary.Signature
import Mathlib.Data.Fin.Rev

/-! # Concrete maximal-Witt finite unitary models -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

section MatrixModel

variable {R : Type*} {C : Type*} [CommRing R] [CommRing C] [Algebra R C]

/-- Coefficient conjugation followed by transpose on actual matrices. -/
def matrixTranspose (σ : AlgebraInvolution R C) (n : ℕ) :
    AlgebraInvolution R (Matrix (Fin n) (Fin n) C) where
  linear :=
    { toFun M i j := σ (M j i)
      map_add' M N := by ext i j; exact σ.apply_add _ _
      map_smul' r M := by ext i j; exact σ.apply_smul _ _ }
  map_one := by
    classical
    ext i j
    change σ ((1 : Matrix (Fin n) (Fin n) C) j i) = _
    by_cases h : i = j
    · subst j; simpa using σ.apply_one
    · simpa [Matrix.one_apply, h, Ne.symm h] using σ.apply_zero
  map_mul M N := by
    ext i j
    change σ.linear (∑ k, M j k * N k i) = ∑ k, σ (N k i) * σ (M j k)
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => σ.apply_mul _ _)
  involutive M := by ext i j; exact σ.apply_apply _

@[simp] theorem matrixTranspose_apply (σ : AlgebraInvolution R C) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C) (i j : Fin n) :
    matrixTranspose σ n M i j = σ (M j i) := rfl

/-- The antidiagonal Gram matrix: hyperbolic pairs and, for odd n, one middle line. -/
def maxWittGram (C : Type*) [CommRing C] (n : ℕ) : Matrix (Fin n) (Fin n) C :=
  fun i j => if i.rev = j then 1 else 0

theorem maxWittGram_sq (n : ℕ) :
    maxWittGram C n * maxWittGram C n = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, maxWittGram]
  rw [Finset.sum_eq_single i.rev]
  · simp [Fin.rev_rev, Matrix.one_apply]
  · intro b _ hne
    simp [Ne.symm hne]
  · simp

theorem maxWittGram_selfAdjoint (σ : AlgebraInvolution R C) (n : ℕ) :
    matrixTranspose σ n (maxWittGram C n) = maxWittGram C n := by
  classical
  ext i j
  change σ (if j.rev = i then 1 else 0) = if i.rev = j then 1 else 0
  have h : (j.rev = i) ↔ (i.rev = j) := by
    constructor <;> intro h <;> simpa using (congrArg Fin.rev h).symm
  simp only [h]
  split_ifs <;> first | exact σ.apply_one | exact σ.apply_zero

/-- The first floor(n/2) coordinates form the standard totally isotropic subspace. -/
theorem maxWittGram_isotropic (n : ℕ) (i j : Fin n)
    (hi : i.val < n / 2) (hj : j.val < n / 2) : maxWittGram C n i j = 0 := by
  have h : i.rev ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_rev] at hv
    omega
  simp [maxWittGram, h]

/-- The nonsingular standard maximal-Witt Gram matrix, whose inverse is itself. -/
def maxWittUnit (n : ℕ) : (Matrix (Fin n) (Fin n) C)ˣ where
  val := maxWittGram C n
  inv := maxWittGram C n
  val_inv := maxWittGram_sq n
  inv_val := maxWittGram_sq n

/-- The actual Hermitian adjoint J^{-1} conjugate-transpose(M) J. -/
def maxWittAdjoint (σ : AlgebraInvolution R C) (n : ℕ) :
    AlgebraInvolution R (Matrix (Fin n) (Fin n) C) :=
  (matrixTranspose σ n).adjoint (maxWittUnit n) (maxWittGram_selfAdjoint σ n)

@[simp] theorem maxWittAdjoint_formula (σ : AlgebraInvolution R C) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C) :
    maxWittAdjoint σ n M = maxWittGram C n * matrixTranspose σ n M * maxWittGram C n := rfl

end MatrixModel

open NumberField _root_.Algebra Langlands.Global
open scoped TensorProduct

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- An actual scalar-compatible split-center identification, including conjugation. -/
structure SplitPlaceIdentification (v : Langlands.Global.FinitePlace E) where
  equiv : LocalCenter E K v ≃ₐ[FiniteCompletion E v]
    (FiniteCompletion E v × FiniteCompletion E v)
  conjugation_eq (z : LocalCenter E K v) :
    equiv (localConjugation E K v z) = Prod.swap (equiv z)

/-- Splitting at the actual finite place is existence of the genuine local-center model. -/
def IsSplitPlace (v : Langlands.Global.FinitePlace E) : Prop :=
  Nonempty (SplitPlaceIdentification E K v)

variable {E K} {A : Type w} [Ring A] [Algebra E A] [Algebra K A]
  [IsScalarTower E K A]

/-- The actual local algebra with involution is the standard maximal-Witt model,
with the specified map from the completed quadratic center. -/
def IsQuasiSplitAt (σ : SecondKindInvolution E K A) (n : ℕ)
    (v : Langlands.Global.FinitePlace E) : Prop :=
  ∃ e : LocalAlgebra E A v ≃ₐ[FiniteCompletion E v]
      Matrix (Fin n) (Fin n) (LocalCenter E K v),
    (∀ z : LocalCenter E K v,
      e (localCenterMap E K A v z) = Matrix.scalar (Fin n) z) ∧
    ∀ x, e (localInvolution σ v x) = maxWittAdjoint (localConjugation E K v) n (e x)

/-- Division at every actual CM completion above the real-field finite place;
at a split place this includes both conjugate places. -/
def IsDivisionAbove (v : Langlands.Global.FinitePlace E) : Prop :=
  ∀ w : Langlands.Global.FinitePlace K, w.asIdeal.LiesOver v.asIdeal → IsDivisionAt K A w

end Langlands.Shimura.FiniteUnitary
