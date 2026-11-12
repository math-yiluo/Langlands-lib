import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Hyperplane sections of an algebra with chosen generators

Let `A` be an `R`-algebra with elements `g : Fin n → A`. For an `R`-algebra `S` and coefficients
`α : Option (Fin n) → S`, the hyperplane element is `α_* ⊗ 1 + ∑ᵢ αᵢ ⊗ gᵢ ∈ S ⊗[R] A` and the
hyperplane section is the quotient of `S ⊗[R] A` by it. This module records how hyperplane
sections behave under base change of `S`, describes their points, and compares them with the
hyperplane sections of a scalar extension `k ⊗[R] A`.
-/

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.Slicing

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} (g : Fin n → A)

/-- The hyperplane element `α_* ⊗ 1 + ∑ᵢ αᵢ ⊗ gᵢ` of `S ⊗[R] A`. -/
noncomputable def hyp {S : Type*} [CommRing S] [Algebra R S] (α : Option (Fin n) → S) :
    S ⊗[R] A :=
  α none ⊗ₜ[R] (1 : A) + ∑ i, α (some i) ⊗ₜ[R] g i

/-- The hyperplane section `(S ⊗[R] A) ⧸ (α_* ⊗ 1 + ∑ᵢ αᵢ ⊗ gᵢ)`. -/
abbrev Slice {S : Type*} [CommRing S] [Algebra R S] (α : Option (Fin n) → S) : Type _ :=
  (S ⊗[R] A) ⧸ Ideal.span {hyp R g α}

variable {R g}

/-- Applying an algebra map to the coefficients transports the hyperplane element. -/
theorem map_hyp {S S' : Type*} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (f : S →ₐ[R] S') (α : Option (Fin n) → S) :
    Algebra.TensorProduct.map f (AlgHom.id R A) (hyp R g α) = hyp R g (f ∘ α) := by
  simp [hyp, map_add, map_sum]

/-- Base change of the coefficient ring transports the hyperplane element. -/
theorem rTensor_hyp {S S' : Type*} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] (α : Option (Fin n) → S) :
    Algebra.TensorProduct.rTensor A (Algebra.ofId S S') (hyp R g α) =
      hyp R g (algebraMap S S' ∘ α) := by
  simp [hyp, map_add, map_sum]

/-- The image of the hyperplane element under `S ⊗[R] A → κ` given by `x : A →ₐ[R] κ`. -/
theorem lift_hyp {S κ : Type*} [CommRing S] [CommRing κ] [Algebra R S] [Algebra R κ]
    [Algebra S κ] [IsScalarTower R S κ] (α : Option (Fin n) → S) (x : A →ₐ[R] κ) :
    Algebra.TensorProduct.liftEquivRight R S A κ x (hyp R g α) =
      algebraMap S κ (α none) + ∑ i, algebraMap S κ (α (some i)) * x (g i) := by
  simp [hyp, map_add, map_sum]

variable (R g)

/-- Base change of hyperplane sections: `S' ⊗[S] Slice α ≃ Slice (α in S')`. -/
noncomputable def sliceBaseChange {S S' : Type*} [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] (α : Option (Fin n) → S) :
    S' ⊗[S] Slice R g α ≃ₐ[S'] Slice R g (algebraMap S S' ∘ α) :=
  (Algebra.tensorQuotientTensorEquiv S' (hyp R g α)).trans
    (Ideal.quotientEquivAlgOfEq S' (by rw [rTensor_hyp]))

/-- Hyperplane sections with equal coefficients are isomorphic. -/
noncomputable def sliceEquivOfEq {S : Type*} [CommRing S] [Algebra R S] {α α' : Option (Fin n) → S}
    (h : α = α') : Slice R g α ≃ₐ[S] Slice R g α' :=
  Ideal.quotientEquivAlgOfEq S (by rw [h])

/-- The points of a hyperplane section with values in an `S`-algebra `κ` are the points of `A`
lying on the hyperplane. -/
noncomputable def slicePointsEquiv {S κ : Type*} [CommRing S] [CommRing κ] [Algebra R S]
    [Algebra R κ] [Algebra S κ] [IsScalarTower R S κ] (α : Option (Fin n) → S) :
    (Slice R g α →ₐ[S] κ) ≃
      {x : A →ₐ[R] κ // algebraMap S κ (α none) + ∑ i, algebraMap S κ (α (some i)) * x (g i) =
        0} where
  toFun φ := ⟨(Algebra.TensorProduct.liftEquivRight R S A κ).symm
      (φ.comp (Ideal.Quotient.mkₐ S _)), by
    rw [← lift_hyp, Equiv.apply_symm_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]⟩
  invFun x := Ideal.Quotient.liftₐ _ (Algebra.TensorProduct.liftEquivRight R S A κ x.1) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, lift_hyp, x.2, mul_zero])
  left_inv φ := by
    apply Ideal.Quotient.algHom_ext
    dsimp only
    rw [Ideal.Quotient.liftₐ_comp, Equiv.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    dsimp only
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_apply]

/-- Hyperplane sections of the scalar extension `k ⊗[R] A`, with generators `1 ⊗ gᵢ`, are the
hyperplane sections of `A`. -/
noncomputable def sliceCancelBaseChange (k : Type*) {S : Type*} [CommRing k] [CommRing S]
    [Algebra R k] [Algebra k S] [Algebra R S] [IsScalarTower R k S]
    (α : Option (Fin n) → S) :
    Slice k (fun i => (1 : k) ⊗ₜ[R] g i) α ≃ₐ[S] Slice R g α :=
  Ideal.quotientEquivAlg _ _ (Algebra.TensorProduct.cancelBaseChange R k S S A) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [hyp, map_add, map_sum, Algebra.TensorProduct.one_def])

end Langlands.AlgebraicGeometry.LangWeil.Slicing
