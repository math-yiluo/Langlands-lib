import Langlands.Algebra.LieCasimir
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter

/-! # The real trace Casimir for the local complex general linear group -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexLocalCasimir

open Langlands.Algebra.LieCasimir Module
open ComplexDuality.LieInvariance (skewRe skewIm)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "L" => (ℂ ⊗[ℝ] M)
local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "I" => Bool × Fin n × Fin n

/-- The real trace form on the complex matrix Lie algebra. -/
def traceForm : LinearMap.BilinForm ℝ M :=
  LinearMap.mk₂ ℝ (fun X Y => (Matrix.trace (X * Y)).re)
    (by intros; simp [Matrix.add_mul, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])
    (by intros; simp [Matrix.mul_add, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])

theorem traceForm_apply (X Y : M) : traceForm n X Y = (Matrix.trace (X * Y)).re := rfl

theorem traceForm_comm (X Y : M) : traceForm n X Y = traceForm n Y X := by
  rw [traceForm_apply, traceForm_apply, Matrix.trace_mul_comm X Y]

theorem traceForm_invariant (X Y Z : M) : traceForm n ⁅X, Y⁆ Z = traceForm n X ⁅Y, Z⁆ := by
  simp only [traceForm_apply, Ring.lie_def, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  apply congrArg Complex.re
  rw [Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.trace_mul_comm Y (X * Z), Matrix.mul_assoc]

private theorem traceForm_single (i j : Fin n) (z : ℂ) (X : M) :
    traceForm n (Matrix.single i j z) X = (z * X j i).re := by
  rw [traceForm_apply, Matrix.trace_single_mul, smul_eq_mul]

theorem traceForm_nondegenerate : (traceForm n).Nondegenerate := by
  have hleft (X : M) (hX : ∀ Y : M, traceForm n Y X = 0) : X = 0 := by
    ext i j
    apply Complex.ext
    · simpa [traceForm_single] using hX (Matrix.single j i 1)
    · have h := hX (Matrix.single j i Complex.I)
      rw [traceForm_single, Complex.mul_re] at h
      simpa using h
  exact ⟨fun X hX => hleft X fun Y => by rw [traceForm_comm, hX], hleft⟩

/-- The real and imaginary parts of the matrix entries, in a single real coordinate space. -/
def matrixCoordinates : M ≃ₗ[ℝ] (I → ℝ) where
  toFun X p := if p.1 then (X p.2.1 p.2.2).im else (X p.2.1 p.2.2).re
  invFun u := Matrix.of fun i j => ⟨u (false, i, j), u (true, i, j)⟩
  left_inv X := by
    ext i j
    rfl
  right_inv u := by
    funext p
    obtain ⟨b, i, j⟩ := p
    cases b <;> rfl
  map_add' X Y := by
    funext p
    obtain ⟨b, i, j⟩ := p
    cases b <;> rfl
  map_smul' t X := by
    funext p
    obtain ⟨b, i, j⟩ := p
    cases b <;> simp [Matrix.smul_apply]

/-- Matrix units and their pure imaginary multiples form the real matrix basis. -/
def matrixRealBasis : Basis I ℝ M :=
  (Pi.basisFun ℝ I).map (matrixCoordinates n).symm

theorem matrixRealBasis_apply (b : Bool) (i j : Fin n) :
    matrixRealBasis n (b, i, j) = Matrix.single i j (if b then Complex.I else 1) := by
  classical
  rw [matrixRealBasis, Basis.map_apply, Pi.basisFun_apply]
  ext k l
  have h : (i = k ∧ j = l) ↔ (k = i ∧ l = j) := by
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  cases b <;>
    simp [matrixCoordinates, Pi.single_apply, Matrix.single_apply, Prod.mk.injEq, h] <;>
      split <;> rfl

private theorem matrixRealBasis_repr (X : M) (b : Bool) (i j : Fin n) :
    (matrixRealBasis n).repr X (b, i, j) = if b then (X i j).im else (X i j).re := by
  rw [matrixRealBasis, Basis.map_repr, LinearEquiv.symm_symm]
  change (Pi.basisFun ℝ I).repr (matrixCoordinates n X) (b, i, j) = _
  rw [Pi.basisFun_repr]
  rfl

private theorem dualBasis_apply (b : Bool) (i j : Fin n) :
    ((traceForm n).dualBasis (traceForm_nondegenerate n) (matrixRealBasis n)) (b, i, j) =
      Matrix.single j i (if b then -Complex.I else 1) := by
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate n).1
  intro X
  rw [LinearMap.BilinForm.sub_left, form_dual_left_eq_repr, matrixRealBasis_repr, traceForm_single]
  cases b <;> simp [Complex.mul_re]

/-- The Lie generator of a real direction in the enveloping algebra of the
complexification. -/
def realGenerator : M →ₗ⁅ℝ⁆ U :=
  { ((UniversalEnvelopingAlgebra.ι ℂ : L →ₗ⁅ℂ⁆ U).toLinearMap.restrictScalars ℝ).comp
      (TensorProduct.mk ℝ ℂ M 1) with
    map_lie' := by
      intro X Y
      change UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] ⁅X, Y⁆) =
        ⁅UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X),
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y)⁆
      rw [← (UniversalEnvelopingAlgebra.ι ℂ).map_lie,
        LieAlgebra.ExtendScalars.bracket_tmul, one_mul] }

private theorem generator_tmul (z : ℂ) (X : M) :
    (UniversalEnvelopingAlgebra.ι ℂ : L →ₗ⁅ℂ⁆ U) (z ⊗ₜ[ℝ] X) =
      z • realGenerator n X := by
  change _ = z • (UniversalEnvelopingAlgebra.ι ℂ : L →ₗ⁅ℂ⁆ U) ((1 : ℂ) ⊗ₜ[ℝ] X)
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The local real trace-form Casimir in the complex enveloping algebra. -/
def matrixCasimir : U :=
  casimirImage (traceForm n) (traceForm_nondegenerate n) (matrixRealBasis n) (realGenerator n)

theorem matrixCasimir_mem_center : matrixCasimir n ∈ Subalgebra.center ℂ U := by
  let S := Subalgebra.centralizer ℂ {matrixCasimir n}
  have hreal (X : M) : realGenerator n X ∈ S := by
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (casimirImage_commutes_generator (traceForm n) (traceForm_nondegenerate n)
      (traceForm_invariant n) (matrixRealBasis n) (realGenerator n) X).symm
  have hcomplex (X : L) : (UniversalEnvelopingAlgebra.ι ℂ : L →ₗ⁅ℂ⁆ U) X ∈ S := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      rw [generator_tmul]
      exact S.smul_mem (hreal X) z
    | add X Y hX hY =>
      simpa only [map_add] using S.add_mem hX hY
  let gen : L →ₗ⁅ℂ⁆ U := UniversalEnvelopingAlgebra.ι ℂ
  have hle : Algebra.adjoin ℂ (Set.range gen) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨X, rfl⟩
    exact hcomplex X
  rw [Subalgebra.mem_center_iff]
  intro a
  have ha : a ∈ Algebra.adjoin ℂ (Set.range gen) := by
    change a ∈ Algebra.adjoin ℂ (Set.range (UniversalEnvelopingAlgebra.ι ℂ : L →ₗ⁅ℂ⁆ U))
    rw [enveloping_adjoin_range]
    trivial
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle ha) _ (Set.mem_singleton _)).symm

theorem matrixCasimir_eq_sum :
    matrixCasimir n =
      (∑ i : Fin n, ∑ j : Fin n,
        realGenerator n (Matrix.single i j 1) * realGenerator n (Matrix.single j i 1)) -
      (∑ i : Fin n, ∑ j : Fin n,
        realGenerator n (Matrix.single i j Complex.I) *
          realGenerator n (Matrix.single j i Complex.I)) := by
  simp [matrixCasimir, casimirImage, Fintype.sum_prod_type, matrixRealBasis_apply,
    dualBasis_apply, ← Matrix.single_neg, map_neg, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg,
    add_comm]

/-- The sum of squares in the real and imaginary matrix directions. -/
def coordinateSquareSum : U :=
  (∑ i : Fin n, ∑ j : Fin n, realGenerator n (Matrix.single i j 1) ^ 2) +
    (∑ i : Fin n, ∑ j : Fin n, realGenerator n (Matrix.single i j Complex.I) ^ 2)

/-- The compact square sum, with ordered pairs of matrix-unit directions. -/
def compactSquareSum : U :=
  (1 / 4 : ℂ) • ∑ i : Fin n, ∑ j : Fin n,
    (realGenerator n (skewRe i j) ^ 2 + realGenerator n (skewIm i j) ^ 2)

private theorem sum_sub_square (A : Fin n → Fin n → U) :
    (∑ i, ∑ j, (A i j - A j i) ^ 2) =
      (2 : ℂ) • ((∑ i, ∑ j, A i j ^ 2) - (∑ i, ∑ j, A i j * A j i)) := by
  have h₁ : (∑ i, ∑ j, A j i ^ 2) = ∑ i, ∑ j, A i j ^ 2 := Finset.sum_comm
  have h₂ : (∑ i, ∑ j, A j i * A i j) = ∑ i, ∑ j, A i j * A j i := Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, (A i j ^ 2 + A j i ^ 2 - (A i j * A j i + A j i * A i j)) := by
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      noncomm_ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h₁, h₂, two_smul]
      abel

private theorem sum_add_square (A : Fin n → Fin n → U) :
    (∑ i, ∑ j, (A i j + A j i) ^ 2) =
      (2 : ℂ) • ((∑ i, ∑ j, A i j ^ 2) + (∑ i, ∑ j, A i j * A j i)) := by
  have h₁ : (∑ i, ∑ j, A j i ^ 2) = ∑ i, ∑ j, A i j ^ 2 := Finset.sum_comm
  have h₂ : (∑ i, ∑ j, A j i * A i j) = ∑ i, ∑ j, A i j * A j i := Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, (A i j ^ 2 + A j i ^ 2 + (A i j * A j i + A j i * A i j)) := by
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      noncomm_ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, h₁, h₂, two_smul]
      abel

/-- The coordinate square sum differs from the central trace Casimir by twice
the compact square sum. -/
theorem coordinateSquareSum_eq_casimir_add_compact :
    coordinateSquareSum n = matrixCasimir n + (2 : ℂ) • compactSquareSum n := by
  simp only [coordinateSquareSum, matrixCasimir_eq_sum, compactSquareSum, skewRe, skewIm,
    map_sub, map_add, Finset.sum_add_distrib]
  rw [sum_sub_square n (fun i j => realGenerator n (Matrix.single i j 1)),
    sum_add_square n (fun i j => realGenerator n (Matrix.single i j Complex.I))]
  module

end Langlands.Archimedean.ComplexLocalCasimir
