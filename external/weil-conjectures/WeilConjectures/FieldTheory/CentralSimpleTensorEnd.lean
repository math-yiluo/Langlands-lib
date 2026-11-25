/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Azumaya.Defs
import WeilConjectures.FieldTheory.CentralSimpleTensorInjective
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The enveloping algebra of a central simple algebra

Source: Stacks Project, Tag 074I, Lemma 11.4.10.
(blueprint: lem-sc-central-simple-tensor-end).
-/

@[expose] public section

universe u

namespace Field

/-- Left and right multiplication identify the enveloping algebra of a finite-dimensional
central simple algebra with its linear endomorphisms.

Proof: the opposite algebra is again central simple, and the tensor product of two
finite-dimensional central simple algebras is simple (Stacks Tags 074G and 074I).
The unital algebra homomorphism `a ⊗ op(b) ↦ (v ↦ a * v * b)` is therefore injective:
its kernel is a two-sided ideal, and cannot be the whole ring because it preserves one.
Both the tensor product and the endomorphism algebra have dimension `(dim_K A)^2`.
An injective linear map between finite-dimensional spaces of equal dimension is
surjective. This proves bijectivity of the explicitly constructed map.
Source: Stacks Project, Tag 074I, Lemma 11.4.10.
(blueprint: lem-sc-central-simple-tensor-end). -/
theorem centralSimple_mulLeftRight_bijective (K : Type u) [Field K] (A : CSA.{u, u} K) :
    Function.Bijective (AlgHom.mulLeftRight K A) := by
  have hi := centralSimple_mulLeftRight_injective K A
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight K A).toLinearMap) ?_).mp hi
  rw [Module.finrank_tensorProduct, Module.finrank_linearMap, MulOpposite.finrank]

end Field
