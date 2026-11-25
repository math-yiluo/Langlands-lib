/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Presentations of tensor maps

Source: Stacks Project, Algebra, proof of Tag 07RI.
(blueprint: lem-weil-pbc-tensor-map-polynomial-presentation).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Base change preserves the variables and coefficientwise relations of a presentation.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47640-47642.
(blueprint: lem-weil-pbc-tensor-map-polynomial-presentation).

Proof: base change the presentation along B → T tensor B. Its target is
(T tensor B) tensor_B C. Commute the two tensor factors, commute T tensor B,
apply tensor cancellation, and commute once more to identify this target with
T tensor C. On pure tensors this is (t tensor b) tensor c ↦ t tensor φ(b)c.
In particular its restriction to T tensor B is id_T tensor φ. Transport the
base-changed presentation through this algebra equivalence. Its relations are
exactly the coefficientwise images of the original relations, by the definition
of Presentation.baseChange. No flatness is required: the quotient/base-change
identification uses right exactness only. Empty generators and relations, and
zero rings, are included by the same constructions. -/
theorem tensorMap_polynomialPresentation
    {A : Type u} [CommRing A]
    {B C : Type v} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C)
    {n m : ℕ} :
    letI : Algebra B C := φ.toRingHom.toAlgebra
    ∀ (P : Presentation B C (Fin n) (Fin m))
      (T : Type u) [CommRing T] [Algebra A T],
      let ψ := TensorProduct.map (AlgHom.id A T) φ
      letI : Algebra (T ⊗[A] B) (T ⊗[A] C) := ψ.toRingHom.toAlgebra
      ∃ Q : Presentation (T ⊗[A] B) (T ⊗[A] C) (Fin n) (Fin m),
        Q.relation = fun j ↦ MvPolynomial.map
          (TensorProduct.includeRight.toRingHom : B →+* T ⊗[A] B) (P.relation j) := by
  let : Algebra B C := φ.toRingHom.toAlgebra
  intro P T _ _
  let : IsScalarTower A B C := IsScalarTower.of_algHom φ
  let ψ := TensorProduct.map (AlgHom.id A T) φ
  let : Algebra (T ⊗[A] B) (T ⊗[A] C) := ψ.toRingHom.toAlgebra
  let : Algebra B (T ⊗[A] B) := TensorProduct.rightAlgebra
  let e₁ := TensorProduct.comm B (T ⊗[A] B) C
  let e₂ := TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[B] C) (TensorProduct.commRight A B T).symm
  let e₃ := TensorProduct.cancelBaseChange A B B C T
  let e₄ := TensorProduct.comm A C T
  let e := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
    (e₃.toRingEquiv.trans e₄.toRingEquiv))
  let E : (T ⊗[A] B) ⊗[B] C ≃ₐ[T ⊗[A] B] T ⊗[A] C :=
    { e with
      commutes' := by
        intro x
        change e (x ⊗ₜ[B] 1) = ψ x
        induction x using TensorProduct.inductionOn with
        | tmul t b => simp [e, e₁, e₂, e₃, e₄, ψ, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        | add x y hx hy =>
          simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy }
  exact ⟨(P.baseChange (T ⊗[A] B)).ofAlgEquiv E, rfl⟩

end Algebra
