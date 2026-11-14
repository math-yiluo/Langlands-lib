import Langlands.GroupScheme.Quaternionic.TorusRowWeightGeometry
import Langlands.GroupScheme.Quaternionic.PolarWeightDuality
import Langlands.GroupScheme.Quaternionic.SubspaceIsometryExtension

/-! # Opposite full-torus row weights have equal dimension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true

namespace Langlands.GroupScheme.Quaternionic

namespace TorusPolarWeightDuality

open MatrixNormOneSplitRank (coeffTensor coeffTensor_tmul)

section Alternating

variable {K A : Type u} [CommRing K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A)

/-- The polar part of an alternating element vanishes. -/
theorem add_involution_eq_zero_of_mem {z : A} (hz : z ∈ τ.alternatingSubspace) :
    z + τ z = 0 := by
  obtain ⟨a, rfl⟩ := τ.mem_alternatingSubspace.mp hz
  rw [FirstKindInvolution.map_sub, FirstKindInvolution.apply_apply]
  abel

end Alternating

section Algebra

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A)

/-- Preserving a quadratic class implies preserving its polar element. -/
theorem polar_defect_eq_zero (Q : A) {R : Type u} [CommRing R] [Algebra K R]
    (y : R ⊗[K] A)
    (hy : IsometryCut.defect τ Q y ∈ τ.alternatingSubspace.baseChange R) :
    IsometryCut.defect τ (Q + τ Q) y = 0 := by
  rw [IsometryCut.alternatingSubspace_baseChange,
    Submodule.restrictScalars_mem] at hy
  have h := add_involution_eq_zero_of_mem (τ.baseChange R) hy
  simp only [IsometryCut.defect, FirstKindInvolution.map_sub,
    FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply,
    FirstKindInvolution.baseChange_tmul] at h ⊢
  rw [TensorProduct.tmul_add, mul_add, add_mul]
  simp only [mul_assoc] at h ⊢
  convert h using 1
  abel

variable {Λ : Type u} [AddCommMonoid Λ] [DecidableEq Λ]

/-- Coefficients of a finite Laurent congruence expression. -/
theorem coeffTensor_congruence_sum (Q : A) (s : Finset Λ) (e : Λ → A) (ν : Λ) :
    coeffTensor A ν
      ((∑ m ∈ s, AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] e m) *
        ((1 : AddMonoidAlgebra K Λ) ⊗ₜ[K] Q) *
        τ.baseChange (AddMonoidAlgebra K Λ)
          (∑ m ∈ s, AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] e m)) =
    ∑ m ∈ s, ∑ p ∈ s, if m + p = ν then e m * Q * τ (e p) else 0 := by
  simp only [FirstKindInvolution.baseChange_tmul,
    Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    AddMonoidAlgebra.single_mul_single, mul_one, map_sum, coeffTensor_tmul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_comm]

/-- Orthogonal idempotents extract a single block from a coefficient matrix. -/
theorem idempotent_mul_coefficient_mul (Q : A) (s : Finset Λ) (e : Λ → A)
    (he : ∀ m p, e m * e p = if m = p then e m else 0)
    (m p : Λ) (hm : m ∈ s) (hp : p ∈ s) (ν : Λ) :
    e m * (∑ a ∈ s, ∑ b ∈ s,
        if a + b = ν then e a * Q * τ (e b) else 0) * τ (e p) =
      if m + p = ν then e m * Q * τ (e p) else 0 := by
  have hterm (a b : Λ) :
      e m * (if a + b = ν then e a * Q * τ (e b) else 0) * τ (e p) =
        if m = a then if p = b then
          if m + p = ν then e m * Q * τ (e p) else 0 else 0 else 0 := by
    by_cases hma : m = a
    · subst a
      by_cases hpb : p = b
      · subst b
        by_cases hmp : m + p = ν
        · simp only [hmp, ite_true]
          calc e m * (e m * Q * τ (e p)) * τ (e p) =
                (e m * e m) * Q * τ (e p * e p) := by
                  rw [FirstKindInvolution.map_mul]
                  simp only [mul_assoc]
          _ = e m * Q * τ (e p) := by rw [he, he, ite_eq_left rfl, ite_eq_left rfl]
        · simp [hmp]
      · rw [ite_eq_left rfl, ite_eq_right hpb]
        by_cases hab : m + b = ν
        · rw [ite_eq_left hab]
          calc e m * (e m * Q * τ (e b)) * τ (e p) =
                (e m * e m) * Q * τ (e p * e b) := by
                  rw [FirstKindInvolution.map_mul]
                  simp only [mul_assoc]
          _ = 0 := by simp [he, hpb]
        · simp [hab]
    · rw [ite_eq_right hma]
      by_cases hab : a + b = ν
      · rw [ite_eq_left hab]
        calc e m * (e a * Q * τ (e b)) * τ (e p) =
              (e m * e a) * Q * τ (e p * e b) := by
                rw [FirstKindInvolution.map_mul]
                simp only [mul_assoc]
        _ = 0 := by simp [he, hma]
      · simp [hab]
  simp only [Finset.mul_sum, Finset.sum_mul, hterm]
  simp [hm, hp]

/-- An invariant Laurent congruence has no block between nonopposite weights. -/
theorem idempotent_block_eq_zero_of_congruence (Q : A) (s : Finset Λ) (e : Λ → A)
    (he : ∀ m p, e m * e p = if m = p then e m else 0)
    (hcong :
      (∑ m ∈ s, AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] e m) *
        ((1 : AddMonoidAlgebra K Λ) ⊗ₜ[K] Q) *
        τ.baseChange (AddMonoidAlgebra K Λ)
          (∑ m ∈ s, AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] e m) =
        (1 : AddMonoidAlgebra K Λ) ⊗ₜ[K] Q)
    (m p : Λ) (hm : m ∈ s) (hp : p ∈ s) (hmp : m + p ≠ 0) :
    e m * Q * τ (e p) = 0 := by
  have hc := congrArg (coeffTensor A (m + p)) hcong
  rw [coeffTensor_congruence_sum] at hc
  simp only [coeffTensor_tmul, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply,
    ite_eq_right (Ne.symm hmp), zero_smul] at hc
  have h := congrArg (fun z : A => e m * z * τ (e p)) hc
  rw [idempotent_mul_coefficient_mul τ Q s e he m p hm hp] at h
  simpa only [ite_true, mul_zero, zero_mul] using h

end Algebra

end TorusPolarWeightDuality

namespace FirstKindInvolution

open FiniteAlgebraUnits FiniteAlgebraTorusWeights FiniteMatrixAlgebraTorusWeights
  SplitTorusRepresentationWeights TorusPolarWeightDuality

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  {I : Type u} [Fintype I] [DecidableEq I]

/-- The block of the polar Gram matrix between two universal row weights. -/
def torusPolarWeightBlock (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m p : I → ℤ) : Matrix n n D :=
  weightElement (i ≫ σ.isometryGroupι q) m * σ.polar q *
    σ.matrix n (weightElement (i ≫ σ.isometryGroupι q) p)

/-- The polar Gram matrix has only opposite-weight blocks. -/
theorem torusPolarWeightBlock_eq_zero (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m p : I → ℤ) (hmp : m + p ≠ 0) :
    σ.torusPolarWeightBlock q i m p = 0 := by
  classical
  set j := i ≫ σ.isometryGroupι q
  let s := weightSupport (rightRegularRepresentation
    (Module.finBasis K (Matrix n n D))) I j
  change weightElement j m * σ.polar q * σ.matrix n (weightElement j p) = 0
  by_cases hm : m ∈ s
  · by_cases hp : p ∈ s
    · have hu : IsometryCut.defect (σ.matrix n) (Quotient.out q)
          ((universalUnit j :
            (AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D)ˣ) :
              AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D) ∈
          (σ.quadraticKernel n).baseChange (AddMonoidAlgebra K (I → ℤ)) := by
        have h := QuadraticTorusWittBound.defect_affinePoint_mem σ q
          (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ)))
          (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom)
        rw [Category.assoc] at h
        exact h
      have hv := (IsometryCut.isometrySubgroup
        (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
        (AddMonoidAlgebra K (I → ℤ))).inv_mem (x := universalUnit j) hu
      rw [IsometryCut.mem_isometrySubgroup, universalUnit_inv_eq_sum] at hv
      have h := polar_defect_eq_zero (σ.matrix n) (Quotient.out q) _ hv
      have hpolar : σ.polar q = Quotient.out q + σ.matrix n (Quotient.out q) := by
        rw [← σ.polar_mk, Submodule.Quotient.mk_out]
      rw [← hpolar, IsometryCut.defect, sub_eq_zero] at h
      exact idempotent_block_eq_zero_of_congruence (σ.matrix n) (σ.polar q) s
        (weightElement j) (weightElement_mul j) h m p hm hp hmp
    · rw [weightElement_eq_zero j hp]
      simp
  · rw [weightElement_eq_zero j hm]
    simp

/-- Row weight spaces are polar-orthogonal unless their exponents sum to zero. -/
theorem sesqForm_eq_zero_of_mem_torusRowWeightSpace (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m p : I → ℤ) (hmp : m + p ≠ 0)
    {x y : n → D} (hx : x ∈ σ.torusRowWeightSpace q i m)
    (hy : y ∈ σ.torusRowWeightSpace q i p) :
    σ.sesqForm (σ.polar q) x y = 0 := by
  have hx' := (mem_rowWeightSpace (i ≫ σ.isometryGroupι q) m x).mp hx
  have hy' := (mem_rowWeightSpace (i ≫ σ.isometryGroupι q) p y).mp hy
  rw [← hx', ← hy', SubspaceScheme.sesqForm_vecMul_vecMul]
  change σ.sesqForm (σ.torusPolarWeightBlock q i m p) x y = 0
  rw [σ.torusPolarWeightBlock_eq_zero q i m p hmp]
  simp [sesqForm]

/-- Nondegeneracy identifies the dimensions of opposite full-torus row weights. -/
theorem finrank_torusRowWeightSpace_eq_neg (q : σ.QuadraticForms n)
    (hq : σ.IsNondegenerateQuadratic q)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m : I → ℤ) :
    Module.finrank D (σ.torusRowWeightSpace q i m) =
      Module.finrank D (σ.torusRowWeightSpace q i (-m)) := by
  apply σ.finrank_eq_neg_of_polar_orthogonal q hq (σ.torusRowWeightSpace q i)
    (iSup_rowWeightSpace_eq_top (i ≫ σ.isometryGroupι q))
  intro a b hab x hx y hy
  exact σ.sesqForm_eq_zero_of_mem_torusRowWeightSpace q i a b hab hx hy

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
