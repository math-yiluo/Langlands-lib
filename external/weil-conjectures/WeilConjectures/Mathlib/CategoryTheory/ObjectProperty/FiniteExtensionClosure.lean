/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import Mathlib.CategoryTheory.Triangulated.Generators

/-! # Finite extension presentations of thick envelopes

Source: Stacks, Tags 0FX1 and 0FX2, and blueprint scalar-six-ctf (1).
(blueprint: lem-sfb-thick-envelope-finite-extensions).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Finite sums and intermediate retracts in a thick envelope can be collected into
finite extension products followed by one final retract.

Source: Stacks, Tags 0FX1 and 0FX2; blueprint scalar-six-ctf (1), finite generators.
(blueprint: lem-sfb-thick-envelope-finite-extensions).

Proof: Let Q be the union of the retract closures of the iterated extension products
of the shift closure of P. Retracts compose, and shifts preserve the same iteration.
For an extension of objects in iterations p and q, the retract-extension lemma moves
both splittings outside the triangle, and associativity gives iteration (p+1)+q.
Thus Q is extension closed. A nonempty generator gives an object in Q; the rotation
of its identity triangle gives zero in Q. Consequently Q is thick, and the universal
property of the thick envelope gives the claimed inclusion. -/
theorem triangEnvelope_le_finiteExtensions (P : ObjectProperty C) [P.Nonempty] :
    P.triangEnvelope ≤ fun K ↦ ∃ n : ℕ,
      ((P.shiftClosure ℤ).extensionProductIter n).retractClosure K := by
  let S := P.shiftClosure ℤ
  let Q : ObjectProperty C := fun K ↦ ∃ n : ℕ, (S.extensionProductIter n).retractClosure K
  have hP : P ≤ Q := fun K hK ↦
    ⟨0, le_retractClosure _ K ((le_shiftClosure P) K hK)⟩
  have : Q.IsStableUnderRetracts := ⟨fun r ⟨n, hn⟩ ↦
    ⟨n, (S.extensionProductIter n).retractClosure.prop_of_retract r hn⟩⟩
  have : Q.IsStableUnderShift ℤ :=
    ⟨fun a ↦ IsStableUnderShiftBy.mk (fun K ⟨n, hn⟩ ↦
      ⟨n, IsStableUnderShiftBy.le_shift K hn⟩)⟩
  have : Q.IsTriangulatedClosed₂ := IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    obtain ⟨p, hp⟩ := h₁
    obtain ⟨q, hq⟩ := h₃
    refine ⟨(p + 1) + q, ?_⟩
    rw [extensionProductIter_add S rfl]
    exact extensionProduct_retractClosure_retractClosure_le _ _ _
      ⟨_, _, _, _, _, hT, hp, hq⟩)
  have hQ : Q P.arbitrary := hP _ P.prop_arbitrary
  have : Q.ContainsZero := ⟨⟨0, isZero_zero C,
    Q.ext_of_isTriangulatedClosed₂ _
      (rot_of_distTriang _ (contractible_distinguished P.arbitrary))
      hQ (Q.le_shift _ _ hQ)⟩⟩
  have : Q.IsTriangulated := {}
  exact (triangEnvelope_le_iff P).mpr hP

end CategoryTheory.ObjectProperty
