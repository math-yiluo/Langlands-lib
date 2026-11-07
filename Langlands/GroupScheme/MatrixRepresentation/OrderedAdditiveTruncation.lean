import Langlands.Algebra.PolynomialBoxQuotient
import Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveProducts

/-! # Bounded nilpotent tests for ordered additive-subgroup actions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveTruncation

open OrderedAdditiveProducts AdditiveDividedPowers
open Langlands.Algebra.PolynomialBoxQuotient

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : GroupScheme (Spec (.of k))} {d : ℕ}
    (ρ : MatrixRepresentation G n)
    (x : Fin d → (VectorGroup.groupScheme (.of k) 1 ⟶ G))

/-- The actual ordered divided-power product, with no interchange of factors. -/
def coefficientOperator (a : Fin d →₀ ℕ) : Module.End k (n → k) :=
  (List.ofFn fun i => dividedPower (ρ.restrict (x i)) (a i)).prod

/-- The polynomial orbit of a vector under the specified ordered subgroup family. -/
def orbitPolynomial (v : n → k) : n → MvPolynomial (Fin d) k :=
  actionPolynomial ρ x *ᵥ fun j => MvPolynomial.C (v j)

theorem orbitPolynomial_coeff (v : n → k) (a : Fin d →₀ ℕ) (i : n) :
    (orbitPolynomial ρ x v i).coeff a = coefficientOperator ρ x a v i := by
  rw [coefficientOperator, ← orderedCoefficients_eq_prod]
  change _ = (Matrix.toLin' (fun r s =>
    (actionPolynomial ρ x r s).coeff a)) v i
  simp only [orbitPolynomial, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm _ (MvPolynomial.C (v j)), MvPolynomial.coeff_C_mul, mul_comm]

theorem affineAction_eq_aeval_orbitPolynomial (v : n → k)
    (A : CommAlgCat.{u} k) (t : Fin d → A) :
    ρ.affineAction A (orderedPoint x A t) (fun j => algebraMap k A (v j)) =
      fun i => MvPolynomial.aeval t (orbitPolynomial ρ x v i) := by
  rw [affineAction_apply, ← actionPolynomial_aeval]
  funext i
  simp only [orbitPolynomial, Matrix.mulVec, dotProduct, Matrix.map_apply,
    map_sum, map_mul, MvPolynomial.aeval_C]

/-- Evaluation at the actual universal tuple with bounded nilpotent coordinates. -/
def universalOrbit (N : Fin d →₀ ℕ) (v : n → k) : n → boxAlgebra (k := k) N :=
  fun i => MvPolynomial.aeval (parameter N) (orbitPolynomial ρ x v i)

/-- Every bounded ordered divided-power image is extracted from an actual
nonreduced test-algebra action. -/
theorem universalOrbit_coefficient (N : Fin d →₀ ℕ) (v : n → k)
    (a : Fin d →₀ ℕ) (ha : a ≤ N) (i : n) :
    coefficient N a ha (universalOrbit ρ x N v i) =
      coefficientOperator ρ x a v i := by
  rw [universalOrbit, coefficient_aeval_parameter, orbitPolynomial_coeff]

private theorem eq_sum_coefficients (N : Fin d →₀ ℕ)
    (z : boxAlgebra (k := k) N) :
    z = ∑ a : Set.Iic N, coefficient N a.val a.property z •
      Ideal.Quotient.mkₐ k (boxIdeal N) (MvPolynomial.monomial a.val (1 : k)) := by
  classical
  apply coefficients_injective N
  funext b
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    coefficients_mk, MvPolynomial.coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · simp only [ite_true, mul_one]
    rfl
  · intro a _ hab
    rw [ite_eq_right (fun h => hab (Subtype.ext h)), mul_zero]
  · simp

/-- Every coefficient contraction of an ordered nilpotent-parameter action is
a linear combination of exactly the bounded ordered coefficient images. -/
theorem linearFunctional_affineAction_eq_sum (N : Fin d →₀ ℕ) (v : n → k)
    (A : CommAlgCat.{u} k) (t : Fin d → A)
    (ht : ∀ i, t i ^ (N i + 1) = 0) (ℓ : A →ₗ[k] k) :
    (fun i => ℓ (ρ.affineAction A (orderedPoint x A t)
      (fun j => algebraMap k A (v j)) i)) =
        ∑ a : Set.Iic N,
          ℓ (MvPolynomial.aeval t (MvPolynomial.monomial a.val (1 : k))) •
            coefficientOperator ρ x a.val v := by
  classical
  rw [affineAction_eq_aeval_orbitPolynomial]
  funext i
  change ℓ (MvPolynomial.aeval t (orbitPolynomial ρ x v i)) = _
  have he :
      MvPolynomial.aeval t (orbitPolynomial ρ x v i) =
        lift N t ht (universalOrbit ρ x N v i) := by
    rw [universalOrbit, aeval_parameter, lift_mk]
  rw [he, eq_sum_coefficients N (universalOrbit ρ x N v i)]
  simp only [map_sum, map_smul, universalOrbit_coefficient,
    lift_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- Stability at ordered products of bounded nilpotent additive parameters,
tested over every commutative test algebra by every scalar functional. -/
def IsStableAtNilpotentTuples (N : Fin d →₀ ℕ) (W : Submodule k (n → k)) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : Fin d → A), (∀ i, t i ^ (N i + 1) = 0) →
    ∀ v ∈ W, ∀ ℓ : A →ₗ[k] k,
      (fun i => ℓ (ρ.affineAction A (orderedPoint x A t)
        (fun j => algebraMap k A (v j)) i)) ∈ W

/-- Nilpotent tests detect precisely the ordered coefficient products in the box.
This holds over finite fields as well as infinite fields. -/
theorem isStableAtNilpotentTuples_iff_invariant_coefficients
    (N : Fin d →₀ ℕ) (W : Submodule k (n → k)) :
    IsStableAtNilpotentTuples ρ x N W ↔
      ∀ a : Fin d →₀ ℕ, a ≤ N → ∀ v ∈ W, coefficientOperator ρ x a v ∈ W := by
  constructor
  · intro h a ha v hv
    have hX := h (CommAlgCat.of k (boxAlgebra (k := k) N))
      (parameter N) (parameter_pow N) v hv (coefficient N a ha)
    rw [affineAction_eq_aeval_orbitPolynomial] at hX
    simpa only [coefficient_aeval_parameter, orbitPolynomial_coeff] using hX
  · intro h A t ht v hv ℓ
    rw [linearFunctional_affineAction_eq_sum ρ x N v A t ht ℓ]
    exact W.sum_mem fun a _ => W.smul_mem _ (h a.val a.property v hv)

/-- The span of all scalar contractions of actual ordered nilpotent actions
on a specified vector. -/
def nilpotentOrbitSpan (N : Fin d →₀ ℕ) (v : n → k) : Submodule k (n → k) :=
  Submodule.span k {w | ∃ (A : CommAlgCat.{u} k) (t : Fin d → A),
    (∀ i, t i ^ (N i + 1) = 0) ∧ ∃ ℓ : A →ₗ[k] k,
      w = fun i => ℓ (ρ.affineAction A (orderedPoint x A t)
        (fun j => algebraMap k A (v j)) i)}

/-- The actual nilpotent orbit span equals the span of the bounded ordered
divided-power images, without a rational-point or infinitude hypothesis. -/
theorem nilpotentOrbitSpan_eq (N : Fin d →₀ ℕ) (v : n → k) :
    nilpotentOrbitSpan ρ x N v =
      Submodule.span k (Set.range fun a : Set.Iic N =>
        coefficientOperator ρ x a.val v) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨A, t, ht, ℓ, rfl⟩
    rw [linearFunctional_affineAction_eq_sum ρ x N v A t ht ℓ]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    refine ⟨CommAlgCat.of k (boxAlgebra (k := k) N), parameter N, parameter_pow N,
      coefficient N a.val a.property, ?_⟩
    rw [affineAction_eq_aeval_orbitPolynomial]
    funext i
    exact (universalOrbit_coefficient ρ x N v a.val a.property i).symm

/-- Fixedness at all actual ordered products with bounded nilpotent parameters. -/
def IsFixedAtNilpotentTuples (N : Fin d →₀ ℕ) (v : n → k) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : Fin d → A), (∀ i, t i ^ (N i + 1) = 0) →
    ρ.affineAction A (orderedPoint x A t) (fun j => algebraMap k A (v j)) =
      fun j => algebraMap k A (v j)

/-- The universal tuple detects fixedness by the exact bounded coefficients,
including the constant identity term. -/
theorem isFixedAtNilpotentTuples_iff_coefficients
    (N : Fin d →₀ ℕ) (v : n → k) :
    IsFixedAtNilpotentTuples ρ x N v ↔
      ∀ a : Fin d →₀ ℕ, a ≤ N →
        coefficientOperator ρ x a v = if a = 0 then v else 0 := by
  classical
  constructor
  · intro h a ha
    have hX := h (CommAlgCat.of k (boxAlgebra (k := k) N))
      (parameter N) (parameter_pow N)
    rw [affineAction_eq_aeval_orbitPolynomial] at hX
    funext i
    have hi := congrArg (fun w : n → boxAlgebra (k := k) N =>
      coefficient N a ha (w i)) hX
    have hC := coefficient_aeval_parameter (k := k) N a ha (MvPolynomial.C (v i))
    rw [MvPolynomial.aeval_C] at hC
    simpa only [coefficient_aeval_parameter, orbitPolynomial_coeff, hC,
      MvPolynomial.coeff_C, eq_comm, ite_apply, Pi.zero_apply] using hi
  · intro h A t ht
    rw [affineAction_eq_aeval_orbitPolynomial]
    funext i
    have hP : orbitPolynomial ρ x v i - MvPolynomial.C (v i) ∈ boxIdeal (k := k) N := by
      apply (mem_boxIdeal N _).mpr
      intro a ha
      change MvPolynomial.lcoeff k a
        (orbitPolynomial ρ x v i - MvPolynomial.C (v i)) = 0
      rw [map_sub, sub_eq_zero]
      change (orbitPolynomial ρ x v i).coeff a = (MvPolynomial.C (v i)).coeff a
      rw [orbitPolynomial_coeff]
      simpa only [MvPolynomial.coeff_C, eq_comm, ite_apply, Pi.zero_apply] using
        congrFun (h a ha) i
    have he := aeval_eq_zero_of_mem_boxIdeal N t ht _ hP
    simpa only [map_sub, MvPolynomial.aeval_C, sub_eq_zero] using he

end Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveTruncation
