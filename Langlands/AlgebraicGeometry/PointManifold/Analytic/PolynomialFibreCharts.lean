import Langlands.AlgebraicGeometry.PointManifold.PolynomialCalculus
import Langlands.AlgebraicGeometry.PointManifold.ZeroFibreChart
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Charts on polynomial solution spaces with an invertible Jacobian -/

noncomputable section

open scoped BigOperators ContDiff Classical Matrix

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open MvPolynomial

variable {k τ σ : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Fintype τ] [Fintype σ]

/-- Simultaneous evaluation of polynomial relations. -/
def polynomialRelations (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k) : σ → k :=
  fun j => eval x (p j)

/-- The free coordinates together with all polynomial relations. -/
def polynomialCoordinateMap (p : σ → MvPolynomial (τ ⊕ σ) k)
    (x : (τ ⊕ σ) → k) : (τ → k) × (σ → k) :=
  (fun i => x (.inl i), polynomialRelations p x)

/-- The square Jacobian in the dependent variables, with relations as rows. -/
def polynomialRelationJacobian (p : σ → MvPolynomial (τ ⊕ σ) k)
    (x : (τ ⊕ σ) → k) : Matrix σ σ k :=
  fun j l => eval x (pderiv (.inr l) (p j))

/-- The derivative of the free-coordinate and relation map. -/
def polynomialCoordinateDerivative (p : σ → MvPolynomial (τ ⊕ σ) k)
    (x : (τ ⊕ σ) → k) : ((τ ⊕ σ) → k) →L[k] ((τ → k) × (σ → k)) :=
  (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (.inl i))).prod
    (ContinuousLinearMap.pi (fun j => polynomialDerivative (p j) x))

@[simp] theorem polynomialCoordinateDerivative_apply
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x v : (τ ⊕ σ) → k) :
    polynomialCoordinateDerivative p x v =
      ((fun i => v (.inl i)), fun j => polynomialDerivative (p j) x v) := rfl

theorem hasFDerivAt_polynomialCoordinateMap
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k) :
    HasFDerivAt (polynomialCoordinateMap p) (polynomialCoordinateDerivative p x) x := by
  exact (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_apply (.inl i) x)).prodMk
    (hasFDerivAt_pi.mpr (fun j => hasFDerivAt_polynomial_eval (p j) x))

theorem contDiff_polynomialCoordinateMap
    (p : σ → MvPolynomial (τ ⊕ σ) k) (n : WithTop ℕ∞) :
    ContDiff k n (polynomialCoordinateMap p) := by
  exact (contDiff_pi.mpr (fun i => contDiff_apply k k (.inl i))).prodMk
    (contDiff_pi.mpr (fun j => contDiff_polynomial_eval (p j) n))

theorem polynomialCoordinateDerivative_bijective
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k)
    (hJ : (polynomialRelationJacobian p x).det ≠ 0) :
    Function.Bijective (polynomialCoordinateDerivative p x) := by
  classical
  have hinj : Function.Injective (polynomialCoordinateDerivative p x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hfree : ∀ i, v (.inl i) = 0 := by
      exact fun i => congrFun (congrArg Prod.fst hv) i
    have hdep : polynomialRelationJacobian p x *ᵥ (fun l => v (.inr l)) = 0 := by
      ext j
      have hj := congrFun (congrArg Prod.snd hv) j
      simpa [polynomialCoordinateDerivative, polynomialDerivative_apply,
        Fintype.sum_sum_type, hfree, polynomialRelationJacobian, Matrix.mulVec,
        dotProduct] using hj
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ hdep
    funext i
    cases i with
    | inl i => exact hfree i
    | inr l => exact congrFun hz l
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (polynomialCoordinateDerivative p x).toLinearMap) ?_).mp hinj
  simp [Module.finrank_prod, Fintype.card_sum]

/-- An invertible dependent Jacobian makes the full coordinate derivative an isomorphism. -/
def polynomialCoordinateDerivativeEquiv
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k)
    (hJ : (polynomialRelationJacobian p x).det ≠ 0) :
    ((τ ⊕ σ) → k) ≃L[k] ((τ → k) × (σ → k)) :=
  (LinearEquiv.ofBijective (polynomialCoordinateDerivative p x).toLinearMap
    (polynomialCoordinateDerivative_bijective p x hJ)).toContinuousLinearEquiv

@[simp] theorem polynomialCoordinateDerivativeEquiv_coe
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k)
    (hJ : (polynomialRelationJacobian p x).det ≠ 0) :
    (polynomialCoordinateDerivativeEquiv p x hJ :
      ((τ ⊕ σ) → k) →L[k] ((τ → k) × (σ → k))) =
        polynomialCoordinateDerivative p x := by
  rfl

private theorem hasStrictFDerivAt_polynomialCoordinateMap
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k) :
    HasStrictFDerivAt (polynomialCoordinateMap p) (polynomialCoordinateDerivative p x) x := by
  have h := ((contDiff_polynomialCoordinateMap p ω).contDiffAt (x := x)).analyticAt.hasStrictFDerivAt
  rwa [(hasFDerivAt_polynomialCoordinateMap p x).fderiv] at h

private def polynomialAmbientChart
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k)
    (hJ : (polynomialRelationJacobian p x).det ≠ 0) :
    OpenPartialHomeomorph ((τ ⊕ σ) → k) ((τ → k) × (σ → k)) :=
  (show HasStrictFDerivAt (polynomialCoordinateMap p)
    (polynomialCoordinateDerivativeEquiv p x hJ :
      ((τ ⊕ σ) → k) →L[k] ((τ → k) × (σ → k))) x from
        hasStrictFDerivAt_polynomialCoordinateMap p x).toOpenPartialHomeomorph
          (polynomialCoordinateMap p)

private theorem polynomialAmbientChart_coe
    (p : σ → MvPolynomial (τ ⊕ σ) k) (x : (τ ⊕ σ) → k)
    (hJ : (polynomialRelationJacobian p x).det ≠ 0) :
    (polynomialAmbientChart p x hJ : ((τ ⊕ σ) → k) → ((τ → k) × (σ → k))) =
      polynomialCoordinateMap p := rfl

/-- A local chart at a solution of polynomial equations whose dependent
Jacobian is nonsingular on the solution space. -/
def polynomialFibreChart
    (p : σ → MvPolynomial (τ ⊕ σ) k)
    (hJ : ∀ x, polynomialRelations p x = 0 → (polynomialRelationJacobian p x).det ≠ 0)
    (x₀ : {x : (τ ⊕ σ) → k // polynomialRelations p x = 0}) :
    OpenPartialHomeomorph {x : (τ ⊕ σ) → k // polynomialRelations p x = 0} (τ → k) :=
  zeroFibreChart (polynomialRelations p)
    (polynomialAmbientChart p x₀.val (hJ x₀.val x₀.property)) (fun _ _ => rfl) x₀

@[simp] theorem polynomialFibreChart_apply
    (p : σ → MvPolynomial (τ ⊕ σ) k)
    (hJ : ∀ x, polynomialRelations p x = 0 → (polynomialRelationJacobian p x).det ≠ 0)
    (x₀ x : {x : (τ ⊕ σ) → k // polynomialRelations p x = 0}) :
    polynomialFibreChart p hJ x₀ x = fun i => x.val (.inl i) := rfl

theorem mem_polynomialFibreChart_source
    (p : σ → MvPolynomial (τ ⊕ σ) k)
    (hJ : ∀ x, polynomialRelations p x = 0 → (polynomialRelationJacobian p x).det ≠ 0)
    (x₀ : {x : (τ ⊕ σ) → k // polynomialRelations p x = 0}) :
    x₀ ∈ (polynomialFibreChart p hJ x₀).source := by
  exact (show HasStrictFDerivAt (polynomialCoordinateMap p)
    (polynomialCoordinateDerivativeEquiv p x₀.val (hJ x₀.val x₀.property) :
      ((τ ⊕ σ) → k) →L[k] ((τ → k) × (σ → k))) x₀.val from
        hasStrictFDerivAt_polynomialCoordinateMap p x₀.val).mem_toOpenPartialHomeomorph_source

theorem polynomialFibreChart_contDiffOn_symm_val
    (p : σ → MvPolynomial (τ ⊕ σ) k)
    (hJ : ∀ x, polynomialRelations p x = 0 → (polynomialRelationJacobian p x).det ≠ 0)
    (x₀ : {x : (τ ⊕ σ) → k // polynomialRelations p x = 0}) :
    ContDiffOn k ω (fun y => ((polynomialFibreChart p hJ x₀).symm y).val)
      (polynomialFibreChart p hJ x₀).target := by
  apply zeroFibreChart_contDiffOn_symm_val
  · intro x _ _
    exact (contDiff_polynomialCoordinateMap p ω).contDiffAt
  · intro x _ hx
    refine ⟨polynomialCoordinateDerivativeEquiv p x (hJ x hx), ?_⟩
    simpa only [polynomialAmbientChart_coe, polynomialCoordinateDerivativeEquiv_coe]
      using hasFDerivAt_polynomialCoordinateMap p x

/-- Every polynomial function is analytic when evaluated along the inverse chart. -/
theorem polynomialFibreChart_contDiffOn_symm_eval
    (p : σ → MvPolynomial (τ ⊕ σ) k)
    (hJ : ∀ x, polynomialRelations p x = 0 → (polynomialRelationJacobian p x).det ≠ 0)
    (x₀ : {x : (τ ⊕ σ) → k // polynomialRelations p x = 0})
    (q : MvPolynomial (τ ⊕ σ) k) :
    ContDiffOn k ω (fun y => eval ((polynomialFibreChart p hJ x₀).symm y).val q)
      (polynomialFibreChart p hJ x₀).target :=
  (contDiff_polynomial_eval q ω).comp_contDiffOn
    (polynomialFibreChart_contDiffOn_symm_val p hJ x₀)

end Langlands.AlgebraicGeometry.PointManifold.Analytic
