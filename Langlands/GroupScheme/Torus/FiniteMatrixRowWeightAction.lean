import Langlands.GroupScheme.Torus.FiniteMatrixRowWeights
import Langlands.GroupScheme.Quaternionic.TensorMatrixComparison
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # All-test row weights of a split torus in a finite matrix algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FiniteAlgebraTorusWeights

open FiniteAlgebraUnits SplitTorusRepresentationWeights

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {d : ℕ} {b : Module.Basis (Fin d) K A}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- Evaluation of the universal inverse unit at any coefficient-algebra point. -/
theorem affineUnit_inv_eq_sum (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) R) :
    (((affinePointsEquiv b R (t ≫ i.hom.hom))⁻¹ : (R ⊗[K] A)ˣ) : R ⊗[K] A) =
      ∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
        (splitTorus.exponentValue I (splitTorus.algebraPointsEquiv I R t)
          (Multiplicative.ofAdd m) : R) ⊗ₜ[K] weightElement i m := by
  let φ := splitTorus.evaluateUnits (R := CommRingCat.of K) I
    (splitTorus.algebraPointsEquiv I R t)
  have ht : Lie.affineMap _ φ (splitTorus.universalPoint (R := CommRingCat.of K) I) = t := by
    rw [splitTorus.universalPoint_evaluateUnits, MulEquiv.symm_apply_apply]
  have hu : affinePointsEquiv b R (t ≫ i.hom.hom) =
      Units.map (Algebra.TensorProduct.map φ (AlgHom.id K A)).toMonoidHom
        (universalUnit i) := by
    rw [← ht]
    change affinePointsEquiv b R
      (((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom φ).op ≫
        splitTorus.universalPoint (R := CommRingCat.of K) I) ≫ i.hom.hom) = _
    rw [Category.assoc]
    exact affinePointsEquiv_naturality b (CommAlgCat.ofHom φ) _
  rw [hu, ← map_inv]
  change Algebra.TensorProduct.map φ (AlgHom.id K A)
    (((universalUnit i)⁻¹ : (AddMonoidAlgebra K (I → ℤ) ⊗[K] A)ˣ) :
      AddMonoidAlgebra K (I → ℤ) ⊗[K] A) = _
  rw [universalUnit_inv_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change splitTorus.evaluateUnits (R := CommRingCat.of K) I
    (splitTorus.algebraPointsEquiv I R t) (AddMonoidAlgebra.single m (1 : K)) ⊗ₜ[K]
      weightElement i m = _
  rw [splitTorus.evaluateUnits_single, map_one, one_mul]

end Langlands.GroupScheme.FiniteAlgebraTorusWeights

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights
open Quaternionic
open MatrixNormOneSplitRank (coeffTensor coeffTensor_tmul)

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {n : Type} [Fintype n] [DecidableEq n]
  {d : ℕ} {b : Module.Basis (Fin d) K (Matrix n n D)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- Inverse right multiplication on coefficient-valued rows. -/
def rowActionOver (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) R) :
    Module.End (R ⊗[K] D) (n → R ⊗[K] D) :=
  (TensorMatrix.equiv R n
    (((affinePointsEquiv b R (t ≫ i.hom.hom))⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
      R ⊗[K] Matrix n n D)).toLinearMapRight'

/-- A pure matrix tensor acts on constant rows by the original matrix. -/
theorem vecMul_equiv_tmul (R : CommAlgCat.{u} (CommRingCat.of K))
    (r : R) (M : Matrix n n D) (v : n → D) :
    (fun a => (1 : R) ⊗ₜ[K] v a) ᵥ* TensorMatrix.equiv R n (r ⊗ₜ[K] M) =
      fun a => r ⊗ₜ[K] (v ᵥ* M) a := by
  funext a
  simp only [TensorMatrix.equiv_tmul, Matrix.vecMul, dotProduct,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]

/-- The torus acts as the sum of its monomial characters times its row projections. -/
theorem rowActionOver_eq_sum (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) R)
    (v : n → D) :
    rowActionOver i R t (fun a => (1 : R) ⊗ₜ[K] v a) =
      ∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
        fun a => (splitTorus.exponentValue I (splitTorus.algebraPointsEquiv I R t)
          (Multiplicative.ofAdd m) : R) ⊗ₜ[K] rowWeightProjection i m v a := by
  unfold rowActionOver
  rw [affineUnit_inv_eq_sum, map_sum]
  change (fun a => (1 : R) ⊗ₜ[K] v a) ᵥ* _ = _
  rw [Matrix.vecMul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact vecMul_equiv_tmul R _ _ v

/-- The universal point detects the row projection as an individual coefficient. -/
theorem coeffTensor_rowActionOver_universal (m : I → ℤ) (v : n → D) (a : n) :
    coeffTensor D m (rowActionOver i
      (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ)))
      (splitTorus.universalPoint (R := CommRingCat.of K) I)
      (fun a => (1 : AddMonoidAlgebra K (I → ℤ)) ⊗ₜ[K] v a) a) =
      rowWeightProjection i m v a := by
  rw [rowActionOver_eq_sum]
  simp only [Finset.sum_apply, map_sum, coeffTensor_tmul]
  simp_rw [splitTorus.exponentValue_universalPoint K I, splitTorus.exponentUnit_val]
  simp only [AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, ite_smul, one_smul, zero_smul]
  by_cases hm : m ∈ weightSupport (rightRegularRepresentation b) I i
  · simp [hm]
  · simp only [Finset.sum_ite_eq', hm, ↓reduceIte]
    change 0 = (v ᵥ* weightElement i m) a
    rw [weightElement_eq_zero i hm, Matrix.vecMul_zero]
    rfl

/-- An idempotent-defined row weight has the expected character on every test algebra. -/
theorem rowActionOver_of_mem (m : I → ℤ) {v : n → D}
    (hv : v ∈ rowWeightSpace i m)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) R) :
    rowActionOver i R t (fun a => (1 : R) ⊗ₜ[K] v a) =
      fun a => (splitTorus.exponentValue I (splitTorus.algebraPointsEquiv I R t)
        (Multiplicative.ofAdd m) : R) ⊗ₜ[K] v a := by
  classical
  rw [rowActionOver_eq_sum]
  simp_rw [rowWeightProjection_of_mem i _ m hv]
  by_cases hm : m ∈ weightSupport (rightRegularRepresentation b) I i
  · funext a
    simp only [Finset.sum_apply, ite_apply, Pi.zero_apply, TensorProduct.tmul_ite]
    simp [hm]
  · have hzero : v = 0 := by
      have h := hv
      rw [rowWeightSpace_eq_bot i hm] at h
      exact h
    subst hzero
    funext a
    simp only [Finset.sum_apply, ite_apply, Pi.zero_apply, TensorProduct.tmul_zero,
      ite_self, Finset.sum_const_zero]

/-- Membership is exactly the character equation over all commutative coefficient algebras. -/
theorem mem_rowWeightSpace_iff_allTest (m : I → ℤ) (v : n → D) :
    v ∈ rowWeightSpace i m ↔
      ∀ (R : CommAlgCat.{u} (CommRingCat.of K))
        (t : GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) R),
        rowActionOver i R t (fun a => (1 : R) ⊗ₜ[K] v a) =
          fun a => (splitTorus.exponentValue I (splitTorus.algebraPointsEquiv I R t)
            (Multiplicative.ofAdd m) : R) ⊗ₜ[K] v a := by
  constructor
  · exact fun hv R t => rowActionOver_of_mem i m hv R t
  · intro hv
    have h := hv (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ)))
      (splitTorus.universalPoint (R := CommRingCat.of K) I)
    rw [splitTorus.exponentValue_universalPoint] at h
    change rowWeightProjection i m v = v
    funext a
    have hc := congrArg (fun w => coeffTensor D m (w a)) h
    rw [coeffTensor_rowActionOver_universal] at hc
    simpa only [splitTorus.exponentUnit_val, coeffTensor_tmul,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul] using hc

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
