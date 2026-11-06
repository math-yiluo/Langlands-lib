import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Coefficients and values of vector-valued polynomials -/

noncomputable section

universe u v w z

namespace Langlands.LinearAlgebra.PolynomialCoefficients

variable {k : Type u} [Field k] {σ : Type v}
  {V : Type w} [AddCommGroup V] [Module k V]
  {W : Type z} [AddCommGroup W] [Module k W]

/-- Evaluation of a finitely supported multivariate polynomial with vector coefficients. -/
def evaluation (t : σ → k) : ((σ →₀ ℕ) →₀ V) →ₗ[k] V :=
  Finsupp.lsum k fun d => (d.prod fun i n => t i ^ n) • LinearMap.id

theorem evaluation_apply (t : σ → k) (P : (σ →₀ ℕ) →₀ V) :
    evaluation t P = P.sum (fun d v => (d.prod fun i n => t i ^ n) • v) :=
  rfl

/-- Applying a linear map to the coefficients commutes with polynomial evaluation. -/
theorem map_evaluation (f : V →ₗ[k] W) (t : σ → k)
    (P : (σ →₀ ℕ) →₀ V) :
    f (evaluation t P) = evaluation t (P.mapRange f f.map_zero) := by
  rw [evaluation_apply, evaluation_apply, Finsupp.sum_mapRange_index]
  · simp only [map_finsuppSum, map_smul]
  · intro d
    exact smul_zero _

/-- Applying a scalar functional gives an ordinary scalar multivariate polynomial. -/
def scalarPolynomial (f : V →ₗ[k] k) (P : (σ →₀ ℕ) →₀ V) :
    MvPolynomial σ k :=
  .ofCoeff (P.mapRange f f.map_zero)

@[simp] theorem scalarPolynomial_coeff (f : V →ₗ[k] k)
    (P : (σ →₀ ℕ) →₀ V) (d : σ →₀ ℕ) :
    (scalarPolynomial f P).coeff d = f (P d) := rfl

theorem eval_scalarPolynomial (f : V →ₗ[k] k) (t : σ → k)
    (P : (σ →₀ ℕ) →₀ V) :
    MvPolynomial.eval t (scalarPolynomial f P) = f (evaluation t P) := by
  rw [map_evaluation]
  change (P.mapRange f f.map_zero).sum
    (fun d c => c * (d.prod fun i n => t i ^ n)) =
      (P.mapRange f f.map_zero).sum
        (fun d c => (d.prod fun i n => t i ^ n) • c)
  apply Finsupp.sum_congr
  intro d _
  exact mul_comm _ _

/-- Over an infinite field, subspace membership of every value recovers every coefficient. -/
theorem coefficient_mem_of_evaluation_mem [Infinite k]
    (P : (σ →₀ ℕ) →₀ V) (S : Submodule k V)
    (h : ∀ t : σ → k, evaluation t P ∈ S) (d : σ →₀ ℕ) :
    P d ∈ S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S (P d)).mp
  intro f hf
  have hP : scalarPolynomial f P = 0 := by
    apply MvPolynomial.funext
    intro t
    rw [eval_scalarPolynomial, map_zero]
    exact (Submodule.mem_dualAnnihilator f).mp hf _ (h t)
  have hc := congrArg (fun Q : MvPolynomial σ k => Q.coeff d) hP
  simpa using hc

/-- A subspace containing every coefficient contains every polynomial value. -/
theorem evaluation_mem_of_coefficient_mem
    (P : (σ →₀ ℕ) →₀ V) (S : Submodule k V)
    (h : ∀ d : σ →₀ ℕ, P d ∈ S) (t : σ → k) :
    evaluation t P ∈ S := by
  rw [evaluation_apply]
  exact S.sum_mem fun d _ => S.smul_mem _ (h d)

theorem evaluation_mem_iff_coefficient_mem [Infinite k]
    (P : (σ →₀ ℕ) →₀ V) (S : Submodule k V) :
    (∀ t : σ → k, evaluation t P ∈ S) ↔ ∀ d : σ →₀ ℕ, P d ∈ S :=
  ⟨fun h d => coefficient_mem_of_evaluation_mem P S h d,
    fun h t => evaluation_mem_of_coefficient_mem P S h t⟩

/-- The values and coefficients of a vector-valued polynomial span the same space. -/
theorem span_range_evaluation_eq_span_range_coefficients [Infinite k]
    (P : (σ →₀ ℕ) →₀ V) :
    Submodule.span k (Set.range fun t : σ → k => evaluation t P) =
      Submodule.span k (Set.range P) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact evaluation_mem_of_coefficient_mem P (Submodule.span k (Set.range P)) (fun d =>
      Submodule.subset_span ⟨d, rfl⟩) t
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact coefficient_mem_of_evaluation_mem P
      (Submodule.span k (Set.range fun t : σ → k => evaluation t P)) (fun t =>
      Submodule.subset_span ⟨t, rfl⟩) d

/-- In any algebra, polynomial values and coefficients generate the same subalgebra. -/
theorem adjoin_range_evaluation_eq_adjoin_range_coefficients [Infinite k]
    {A : Type w} [Ring A] [Algebra k A] (P : (σ →₀ ℕ) →₀ A) :
    Algebra.adjoin k (Set.range fun t : σ → k => evaluation t P) =
      Algebra.adjoin k (Set.range P) := by
  simpa only [Algebra.adjoin_span] using
    congrArg (fun S : Submodule k A => Algebra.adjoin k (S : Set A))
      (span_range_evaluation_eq_span_range_coefficients P)

/-- Evaluation of a polynomial family of linear maps commutes with application. -/
theorem evaluation_apply_linearMap
    (P : (σ →₀ ℕ) →₀ (V →ₗ[k] W)) (t : σ → k) (v : V) :
    (evaluation t P) v =
      evaluation t (P.mapRange (LinearMap.applyₗ v) (map_zero (LinearMap.applyₗ v))) :=
  map_evaluation (LinearMap.applyₗ v) t P

/-- A polynomial family maps a subspace into another exactly when all its coefficients do. -/
theorem mapsTo_evaluation_iff_mapsTo_coefficients [Infinite k]
    (P : (σ →₀ ℕ) →₀ (V →ₗ[k] W)) (S : Submodule k V) (T : Submodule k W) :
    (∀ t : σ → k, Set.MapsTo (evaluation t P : V →ₗ[k] W) S T) ↔
      ∀ d : σ →₀ ℕ, Set.MapsTo (P d) S T := by
  constructor
  · intro h d v hv
    exact coefficient_mem_of_evaluation_mem
      (P.mapRange (LinearMap.applyₗ v) (map_zero (LinearMap.applyₗ v))) T
      (fun t => by rw [← evaluation_apply_linearMap]; exact h t hv) d
  · intro h t v hv
    rw [evaluation_apply_linearMap]
    exact evaluation_mem_of_coefficient_mem _ T (fun d => h d hv) t

/-- Polynomial endomorphism values and their coefficient operators preserve the same subspaces. -/
theorem invariant_evaluation_iff_invariant_coefficients [Infinite k]
    (P : (σ →₀ ℕ) →₀ Module.End k V) (S : Submodule k V) :
    (∀ t : σ → k, ∀ v ∈ S, (evaluation t P) v ∈ S) ↔
      ∀ d : σ →₀ ℕ, ∀ v ∈ S, (P d) v ∈ S :=
  mapsTo_evaluation_iff_mapsTo_coefficients P S S

end Langlands.LinearAlgebra.PolynomialCoefficients
