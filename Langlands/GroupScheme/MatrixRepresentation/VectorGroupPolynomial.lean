import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.LinearAlgebra.PolynomialCoefficientSpan
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Polynomial coefficient operators of actual vector-group representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}} {d : ℕ}

/-- The affine point of the vector group with the given coordinates. -/
def affinePoint (S : CommAlgCat.{u} R) (t : Fin d → S) :
    (algSpec R).obj (op S) ⟶ (groupScheme R d).X :=
  (algSpec R).map (CommAlgCat.ofHom (MvPolynomial.aeval t)).op

@[simp] theorem affinePointsEquiv_affinePoint (S : CommAlgCat.{u} R) (t : Fin d → S) :
    Corepresented.affinePointsEquiv (functor R d) (corepresentableBy R d) S
        (affinePoint S t) = Multiplicative.ofAdd t := by
  rw [affinePoint, Corepresented.affinePointsEquiv_map]
  apply Multiplicative.toAdd.injective
  funext i
  exact MvPolynomial.aeval_X t i

theorem affinePoint_surjective (S : CommAlgCat.{u} R) :
    Function.Surjective (affinePoint (d := d) S) := by
  intro x
  let t : Multiplicative (Fin d → S) :=
    Corepresented.affinePointsEquiv (functor R d) (corepresentableBy R d) S x
  refine ⟨t.toAdd, ?_⟩
  apply (Corepresented.affinePointsEquiv (functor R d) (corepresentableBy R d) S).injective
  exact affinePointsEquiv_affinePoint S t.toAdd

@[simp] theorem affinePoint_zero (S : CommAlgCat.{u} R) :
    affinePoint (d := d) S 0 = 1 := by
  apply (Corepresented.affinePointsEquiv (functor R d) (corepresentableBy R d) S).injective
  rw [affinePointsEquiv_affinePoint, map_one]
  rfl

theorem affinePoint_add (S : CommAlgCat.{u} R) (t t' : Fin d → S) :
    affinePoint S (t + t') = affinePoint S t * affinePoint S t' := by
  apply (Corepresented.affinePointsEquiv (functor R d) (corepresentableBy R d) S).injective
  rw [map_mul, affinePointsEquiv_affinePoint, affinePointsEquiv_affinePoint,
    affinePointsEquiv_affinePoint]
  rfl

end VectorGroup

namespace MatrixRepresentation.VectorGroupPolynomial

section UniversalMatrix

variable {R : CommRingCat.{u}} {d : ℕ} {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix at the universal vector-group point, with polynomial entries. -/
def polynomialMatrix (ρ : MatrixRepresentation (VectorGroup.groupScheme R d) n) :
    Matrix n n (MvPolynomial (Fin d) R) :=
  (ρ.affineMatrix (VectorGroup.coordinateAlgebra R d) (𝟙 _) :
    Matrix n n (MvPolynomial (Fin d) R))

/-- Polynomial evaluation recovers the actual matrix over every commutative test algebra. -/
theorem polynomialMatrix_aeval
    (ρ : MatrixRepresentation (VectorGroup.groupScheme R d) n)
    (S : CommAlgCat.{u} R) (t : Fin d → S) :
    (polynomialMatrix ρ).map (MvPolynomial.aeval t) =
      (ρ.affineMatrix S (VectorGroup.affinePoint S t) : Matrix n n S) := by
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (MvPolynomial.aeval t) : VectorGroup.coordinateAlgebra R d ⟶ S)
    (𝟙 (VectorGroup.groupScheme R d).X)
  have h' := congrArg (fun g : GL n S => (g : Matrix n n S)) h
  change (ρ.affineMatrix S
      ((algSpec R).map (CommAlgCat.ofHom (MvPolynomial.aeval t)).op ≫ 𝟙 _) :
        Matrix n n S) = (polynomialMatrix ρ).map (MvPolynomial.aeval t) at h'
  simpa only [Category.comp_id, VectorGroup.affinePoint] using h'.symm

end UniversalMatrix

section MatrixCoefficients

variable {k : Type u} [Field k] {σ : Type v} {n : Type} [Fintype n] [DecidableEq n]

open Langlands.LinearAlgebra.PolynomialCoefficients

/-- The finitely supported family of coefficient matrices of a polynomial matrix. -/
def matrixCoefficients (M : Matrix n n (MvPolynomial σ k)) :
    (σ →₀ ℕ) →₀ Matrix n n k := by
  classical
  refine Finsupp.onFinset
    (Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (M i j).support)
    (fun a i j => (M i j).coeff a) ?_
  intro a ha
  by_contra h
  apply ha
  ext i j
  have hij : a ∉ (M i j).support := by
    intro hij
    apply h
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, hij⟩⟩
  exact MvPolynomial.notMem_support_iff.mp hij

omit [DecidableEq n] in
@[simp] theorem matrixCoefficients_apply (M : Matrix n n (MvPolynomial σ k))
    (a : σ →₀ ℕ) (i j : n) :
    matrixCoefficients M a i j = (M i j).coeff a := rfl

omit [DecidableEq n] in
/-- Evaluating the finite family of coefficient matrices evaluates each matrix entry. -/
theorem evaluation_matrixCoefficients (M : Matrix n n (MvPolynomial σ k)) (t : σ → k) :
    evaluation t (matrixCoefficients M) = M.map (MvPolynomial.eval t) := by
  ext i j
  let f : Matrix n n k →ₗ[k] k :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : scalarPolynomial f (matrixCoefficients M) = M i j := by
    ext a
    rfl
  have h := eval_scalarPolynomial f t (matrixCoefficients M)
  rw [hf] at h
  exact h.symm

/-- Coefficient matrices, acting on column vectors, form a finite polynomial of operators. -/
def operatorCoefficients (M : Matrix n n (MvPolynomial σ k)) :
    (σ →₀ ℕ) →₀ Module.End k (n → k) :=
  (matrixCoefficients M).mapRange (Matrix.toLin' : Matrix n n k ≃ₗ[k] _)
    (map_zero Matrix.toLin')

@[simp] theorem operatorCoefficients_apply (M : Matrix n n (MvPolynomial σ k))
    (a : σ →₀ ℕ) :
    operatorCoefficients M a = Matrix.toLin' (fun i j => (M i j).coeff a) := rfl

theorem evaluation_operatorCoefficients (M : Matrix n n (MvPolynomial σ k)) (t : σ → k) :
    evaluation t (operatorCoefficients M) = Matrix.toLin' (M.map (MvPolynomial.eval t)) := by
  calc
    evaluation t (operatorCoefficients M) =
        Matrix.toLin' (evaluation t (matrixCoefficients M)) :=
      (map_evaluation (Matrix.toLin' : Matrix n n k ≃ₗ[k] _).toLinearMap t _).symm
    _ = _ := congrArg Matrix.toLin' (evaluation_matrixCoefficients M t)

end MatrixCoefficients

section ActualOperators

variable {k : Type u} [Field k] {d : ℕ} {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) d) n)

open Langlands.LinearAlgebra.PolynomialCoefficients

/-- The actual affine action at a base-field point, as an endomorphism. -/
def pointOperator
    (x : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) d).X) :
    Module.End k (n → k) :=
  (ρ.affineAction (CommAlgCat.of k k) x).toLinearMap

/-- The finitely supported coefficient operators of an actual vector-group representation. -/
def coefficientOperators : ((Fin d →₀ ℕ) →₀ Module.End k (n → k)) :=
  operatorCoefficients (polynomialMatrix ρ)

@[simp] theorem coefficientOperators_apply (a : Fin d →₀ ℕ) :
    coefficientOperators ρ a = Matrix.toLin' (fun i j => (polynomialMatrix ρ i j).coeff a) :=
  rfl

/-- Evaluation of the coefficient operators is the actual action at the classified point. -/
theorem evaluation_coefficientOperators (t : Fin d → k) :
    evaluation t (coefficientOperators ρ) =
      pointOperator ρ (VectorGroup.affinePoint (R := CommRingCat.of k) (d := d) (CommAlgCat.of k k) t) := by
  rw [coefficientOperators, evaluation_operatorCoefficients]
  have h := polynomialMatrix_aeval ρ (CommAlgCat.of k k) t
  rw [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  rfl

theorem pointOperator_one : pointOperator ρ 1 = 1 := by
  unfold pointOperator
  rw [map_one]
  rfl

theorem pointOperator_mul
    (x y : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) d).X) :
    pointOperator ρ (x * y) = pointOperator ρ x * pointOperator ρ y := by
  unfold pointOperator
  rw [map_mul]
  rfl

theorem pointOperator_commute
    (x y : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) d).X) :
    pointOperator ρ x * pointOperator ρ y = pointOperator ρ y * pointOperator ρ x := by
  obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of k) (d := d) (CommAlgCat.of k k) x
  obtain ⟨s, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of k) (d := d) (CommAlgCat.of k k) y
  rw [← pointOperator_mul, ← pointOperator_mul, ← VectorGroup.affinePoint_add,
    ← VectorGroup.affinePoint_add, add_comm t s]

/-- The coefficient operators and all actual affine base-field actions preserve the same
subspaces over an infinite field. -/
theorem invariant_affinePoints_iff_invariant_coefficients [Infinite k]
    (S : Submodule k (n → k)) :
    (∀ x, ∀ v ∈ S, pointOperator ρ x v ∈ S) ↔
      ∀ a : Fin d →₀ ℕ, ∀ v ∈ S, coefficientOperators ρ a v ∈ S := by
  rw [← invariant_evaluation_iff_invariant_coefficients]
  constructor
  · intro h t v hv
    rw [evaluation_coefficientOperators]
    exact h _ v hv
  · intro h x v hv
    obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of k) (d := d) (CommAlgCat.of k k) x
    rw [← evaluation_coefficientOperators]
    exact h t v hv

/-- The linear span of the actual affine point actions is the coefficient-operator span. -/
theorem span_range_pointOperator_eq_span_range_coefficients [Infinite k] :
    Submodule.span k (Set.range (pointOperator ρ)) =
      Submodule.span k (Set.range (coefficientOperators ρ)) := by
  have hr : Set.range (pointOperator ρ) =
      Set.range (fun t : Fin d → k => evaluation t (coefficientOperators ρ)) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of k) (d := d) (CommAlgCat.of k k) x
      exact ⟨t, evaluation_coefficientOperators ρ t⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, (evaluation_coefficientOperators ρ t).symm⟩
  rw [hr]
  exact span_range_evaluation_eq_span_range_coefficients _

/-- The algebra generated by actual affine point actions is generated by the coefficients. -/
theorem adjoin_range_pointOperator_eq_adjoin_range_coefficients [Infinite k] :
    Algebra.adjoin k (Set.range (pointOperator ρ)) =
      Algebra.adjoin k (Set.range (coefficientOperators ρ)) := by
  simpa only [Algebra.adjoin_span] using
    congrArg (fun S : Submodule k (Module.End k (n → k)) =>
      Algebra.adjoin k (S : Set (Module.End k (n → k))))
      (span_range_pointOperator_eq_span_range_coefficients ρ)

/-- Coefficient operators of an actual vector-group representation commute. -/
theorem coefficientOperators_commute [Infinite k] (a b : Fin d →₀ ℕ) :
    coefficientOperators ρ a * coefficientOperators ρ b =
      coefficientOperators ρ b * coefficientOperators ρ a := by
  have hc (c : Fin d →₀ ℕ) :
      coefficientOperators ρ c ∈
        Subalgebra.centralizer k (Set.range (pointOperator ρ)) := by
    apply coefficient_mem_of_evaluation_mem (coefficientOperators ρ)
      (Subalgebra.centralizer k (Set.range (pointOperator ρ))).toSubmodule
    intro t
    rw [evaluation_coefficientOperators]
    rintro _ ⟨x, rfl⟩
    exact pointOperator_commute ρ x _
  have hb : coefficientOperators ρ b ∈
      Subalgebra.centralizer k {coefficientOperators ρ a} := by
    apply coefficient_mem_of_evaluation_mem (coefficientOperators ρ)
      (Subalgebra.centralizer k {coefficientOperators ρ a}).toSubmodule
    intro t
    rw [evaluation_coefficientOperators]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact (((Subalgebra.mem_centralizer_iff k).mp (hc a)) _ ⟨_, rfl⟩).symm
  exact (Subalgebra.mem_centralizer_iff k).mp hb _ (Set.mem_singleton _)

end ActualOperators

end MatrixRepresentation.VectorGroupPolynomial
end Langlands.GroupScheme
