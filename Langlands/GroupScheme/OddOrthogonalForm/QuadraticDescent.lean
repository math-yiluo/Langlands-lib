import Langlands.GroupScheme.OddOrthogonalForm.VectorTrivialization

/-! # Descent of the odd quadratic form through the exact vector cocycle -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix
open OrthogonalMatrix (IsAlt strictUpper isAlt_iff)
open Quaternionic.FirstKindInvolution

section Representatives

variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- Retain the diagonal coefficients and put each mixed coefficient above the diagonal. -/
private def upperRepresentative (M : Matrix ι ι R) : Matrix ι ι R :=
  M + (strictUpper Mᵀ - (strictUpper Mᵀ)ᵀ)

private theorem upperRepresentative_sub (M : Matrix ι ι R) :
    IsAlt (upperRepresentative M - M) := by
  refine ⟨strictUpper Mᵀ, ?_⟩
  unfold upperRepresentative
  abel

private theorem upperRepresentative_eq {M D : Matrix ι ι R} (h : IsAlt (M - D)) :
    upperRepresentative M = upperRepresentative D := by
  obtain ⟨hp, hd⟩ := (isAlt_iff _).mp h
  ext i j
  have hpij := congrFun (congrFun hp i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.zero_apply]
    at hpij
  simp only [upperRepresentative, strictUpper, Matrix.add_apply, Matrix.sub_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy (Fintype.equivFin ι i) (Fintype.equivFin ι j) with hij | hij | hij
  · simp only [hij, lt_asymm hij, ite_true, ite_false, sub_zero]
    linear_combination hpij
  · obtain rfl := (Fintype.equivFin ι).injective hij
    simpa using sub_eq_zero.mp (hd i)
  · simp only [hij, lt_asymm hij, ite_true, ite_false, zero_sub, add_neg_cancel]

private theorem upperRepresentative_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix ι ι R) :
    (upperRepresentative M).map f = upperRepresentative (M.map f) := by
  simp only [upperRepresentative, Matrix.map_add _ (map_add f), Matrix.map_sub _ (map_sub f),
    Matrix.transpose_map, ← OrthogonalMatrix.strictUpper_map]

end Representatives

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}
variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N)) [FiniteDimensional K N]

/-- Congruence of the split representative by the inverse Hilbert-90 basis. -/
private def transformedMatrix (hn : 2 ≤ n) : Matrix (Index (Fin n)) (Index (Fin n)) N :=
  (descentBasis φ hn)⁻¹.val * formMatrix (Fin n) N * ((descentBasis φ hn)⁻¹.val)ᵀ

private theorem transformedMatrix_map_sub (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) :
    IsAlt ((transformedMatrix φ hn).map (σ : N →+* N) - transformedMatrix φ hn) := by
  have h := congrArg (fun z : GL (Index (Fin n)) N => z⁻¹) (descentBasis_spec φ hn σ)
  simp only [mul_inv_rev, ← _root_.map_inv] at h
  have hb := congrArg (fun z : GL (Index (Fin n)) N => z * matrixCocycle φ hn σ) h
  simp only [mul_assoc, inv_mul_cancel, mul_one] at hb
  have hval := congrArg Units.val hb
  change ((descentBasis φ hn)⁻¹.val).map (σ : N →+* N) =
    (descentBasis φ hn)⁻¹.val * (matrixCocycle φ hn σ).val at hval
  let B := (descentBasis φ hn)⁻¹.val
  let c := (matrixCocycle φ hn σ).val
  have hc := (matrixCocycle_equations φ hn σ).1.conj B
  have hQ : (formMatrix (Fin n) N).map (σ : N →+* N) = formMatrix (Fin n) N := by
    rw [formMatrix_map_compare (σ : N →+* N) (RingHom.id N)]
    rfl
  rw [transformedMatrix, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    hQ, hval]
  simpa only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] using hc

variable [IsGalois K N]

private theorem exists_descendedMatrix (hn : 2 ≤ n) :
    ∃ D : Matrix (Index (Fin n)) (Index (Fin n)) K,
      D.map (algebraMap K N) = upperRepresentative (transformedMatrix φ hn) := by
  let M := upperRepresentative (transformedMatrix φ hn)
  have hfixed (σ : N ≃ₐ[K] N) : M.map (σ : N →+* N) = M := by
    dsimp only [M]
    rw [upperRepresentative_map]
    exact upperRepresentative_eq (transformedMatrix_map_sub φ hn σ)
  have h (i j : Index (Fin n)) : ∃ a : K, algebraMap K N a = M i j :=
    (IsGalois.mem_range_algebraMap_iff_fixed (M i j)).2 fun σ =>
      congrFun (congrFun (hfixed σ) i) j
  choose a ha using h
  exact ⟨Matrix.of a, Matrix.ext ha⟩

/-- A ground-field representative of the descended scalar quadratic form. -/
def descendedMatrix (hn : 2 ≤ n) : Matrix (Index (Fin n)) (Index (Fin n)) K :=
  Classical.choose (exists_descendedMatrix φ hn)

/-- The ground-field representative has the required quadratic class after extension. -/
private theorem descendedMatrix_map_sub (hn : 2 ≤ n) :
    IsAlt ((descendedMatrix φ hn).map (algebraMap K N) - transformedMatrix φ hn) := by
  rw [descendedMatrix, Classical.choose_spec (exists_descendedMatrix φ hn)]
  exact upperRepresentative_sub _

/-- The chosen basis identifies the full descended quadratic class with the split class. -/
theorem descentBasis_congruence (hn : 2 ≤ n) :
    IsAlt ((descentBasis φ hn).val * (descendedMatrix φ hn).map (algebraMap K N) *
      (descentBasis φ hn).valᵀ - formMatrix (Fin n) N) := by
  let P := descentBasis φ hn
  have h := (descendedMatrix_map_sub φ hn).conj P.val
  have htr : P.val * transformedMatrix φ hn * P.valᵀ = formMatrix (Fin n) N := by
    rw [transformedMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rwa [Matrix.mul_sub, Matrix.sub_mul, htr] at h

/-- The actual scalar quadratic form on the descended vector coordinates. -/
def descendedForm (hn : 2 ≤ n) : (scalar K).QuadraticForms (Index (Fin n)) :=
  Submodule.Quotient.mk (descendedMatrix φ hn)

end Langlands.GroupScheme.OddOrthogonalForm
