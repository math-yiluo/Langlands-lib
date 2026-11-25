/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.TensorOppositeMatrixLifts

/-!
# Tensor lifts with the quotient scalar defect

Source: Stacks Project, Tag 03R7, injectivity argument; Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- Tensoring projective lifts with inverse transposes gives the quotient scalar defect.

Proof: unpack both scalar-defect realizations, retaining their actual homogeneous
cocycles z and w and their projection equations. The transpose anti-isomorphism identifies
matrices opposite with matrices. Combine it with the second splitting, commute opposite
with scalar extension, and use the first splitting and the Kronecker matrix isomorphism
to split the tensor product over the separable closure. Reindex Fin n × Fin m as Fin (n*m).
For its lifts take the Kronecker product of the first lifts with the inverse transpose
of the second lifts. Inverse transpose is a group homomorphism on invertible matrices,
commutes with coefficient automorphisms, and sends scalar u to scalar u inverse.
Thus the two defect identities multiply to the displayed quotient identity. The
conjugation identity holds on pure tensors by the two original identities, hence on the
whole algebra by bilinearity. Local constancy follows by composing the two locally
constant lifts with inverse transpose and the Kronecker map. The size n*m is nonzero
because both original sizes are nonzero. This step uses no equality of cohomology classes
and supplies only a splitting over the separable closure, not a splitting over K.
Source: Stacks Project, Tag 03R7, direct computation with tensor cocycles.
(blueprint: lem-sc-brauer-scalar-defect-tensor-lifts). -/
theorem exists_tensor_opposite_scalarDefect_lifts (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y) :
    ∃ (n : ℕ) (_ : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] (A ⊗[K] Bᵐᵒᵖ)) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : Gal(SeparableClosure K/K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
      (z w : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2),
      IsLocallyConstant b ∧
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z = x ∧
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom w = y ∧
      (∀ (g : Gal(SeparableClosure K/K)) (a : A ⊗[K] Bᵐᵒᵖ),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n)
          (galoisUnitsCocycleValue K z g h / galoisUnitsCocycleValue K w g h) *
            b (g * h))  := by
  obtain ⟨n, hn, eA, a, hla, z, hz, ha, hda⟩ := hx
  obtain ⟨m, hm, eB, b, hlb, w, hw, hb, hdb⟩ := hy
  obtain ⟨e, he⟩ := exists_tensor_opposite_matrix_conjugation K A B n m eA eB a b ha hb
  refine ⟨n * m, Nat.mul_ne_zero hn hm, e,
    fun g ↦ tensorOppositeMatrixLift (a g) (b g), z, w, ?_, hz, hw, he, ?_⟩
  · exact hla.comp₂ hlb tensorOppositeMatrixLift
  · intro g h
    change tensorOppositeMatrixLift (a g) (b g) *
      Matrix.GeneralLinearGroup.map g.toRingHom (tensorOppositeMatrixLift (a h) (b h)) = _
    obtain ⟨hmap, hmul, hscalar⟩ :=
      tensorOppositeMatrixLift_properties g.toRingHom (a h) (a h) (b h) (b h) 1 1
    have hmul' := (tensorOppositeMatrixLift_properties (R := SeparableClosure K)
      (S := SeparableClosure K)
      (RingHom.id _) (a g) (Matrix.GeneralLinearGroup.map g.toRingHom (a h))
        (b g) (Matrix.GeneralLinearGroup.map g.toRingHom (b h)) 1 1).2.1
    rw [← hmap, ← hmul', hda, hdb]
    obtain ⟨_, hmul2, hscalar2⟩ :=
      tensorOppositeMatrixLift_properties (R := SeparableClosure K) (S := SeparableClosure K)
        (RingHom.id _) (Matrix.GeneralLinearGroup.scalar (Fin n)
          (galoisUnitsCocycleValue K z g h)) (a (g * h))
        (Matrix.GeneralLinearGroup.scalar (Fin m)
          (galoisUnitsCocycleValue K w g h)) (b (g * h))
        (galoisUnitsCocycleValue K z g h) (galoisUnitsCocycleValue K w g h)
    rw [hmul2, hscalar2]


end Field
