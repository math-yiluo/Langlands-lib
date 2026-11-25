/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# The pro-étale site of a separably closed field

Let `k` be a separably closed field. The final object `Spec k` of the pro-étale site of `Spec k`
is weakly contractible (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_self`): every
faithfully flat ind-étale `k`-algebra has a `k`-point.
-/

@[expose] public section

universe w u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.ProEt

variable (k : Type u) [Field k] [IsSepClosed k]

/-- For a separably closed field `k`, the final object `Spec k` of the pro-étale site of `Spec k`
is weakly contractible: a faithfully flat ind-étale `k`-algebra is weakly étale and nonzero, so
it has a `k`-point (`Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed`). -/
theorem isWeaklyContractible_self :
    (topology (Spec (.of k))).IsWeaklyContractible.{w} (ProEt.mk (𝟙 (Spec (.of k)))) :=
  isWeaklyContractible_of_forall_exists_retraction (R := .of k) (fun T _ _ _ _ ↦ by
    have : Nontrivial (k ⊗[k] T) := Module.FaithfullyFlat.rTensor_nontrivial k T k
    have : Nontrivial T := (TensorProduct.lid k T).symm.toEquiv.nontrivial
    obtain ⟨φ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed (K := k) (R := T)
    exact ⟨φ.toRingHom, RingHom.ext fun x ↦ φ.commutes x⟩) (Iso.refl _)

end AlgebraicGeometry.Scheme.ProEt
