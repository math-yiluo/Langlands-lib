/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
import WeilConjectures.AlgebraicGeometry.DualTensorHomComparison

/-! # Dual pairings for finite locally free modules

Source: Stacks Project, Modules, Example 0FNV.
(blueprint: lem-ag-finite-locally-free-dual-pairing)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module and its internal dual admit an exact pairing.

Source: Stacks Project, Modules, Example 0FNV.

Proof: on an open with a basis `m₁, …, mᵣ` of `M`, write `m₁*, …, mᵣ*` for the
dual basis. Evaluation sends `m ⊗ φ` to `φ(m)`. Coevaluation sends `1` to the sum
of `mᵢ* ⊗ mᵢ`. This sum is the inverse image of the identity endomorphism under
`dual M ⊗ M ≅ Hom(M, M)`, so it is independent of the chosen basis. Consequently
these local coevaluations glue to a global morphism. The two triangle identities
can be checked on the same open cover, where each follows by evaluating the finite
sum on a basis vector. For rank zero the sum is empty and both identities hold on
the zero object. Thus these morphisms give an exact pairing with left object
`dual M` and right object `M`.

(blueprint: lem-ag-finite-locally-free-dual-pairing) -/
theorem nonempty_exactPairing_dual_of_isFiniteLocallyFree
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree] :
    Nonempty (ExactPairing (dual M) M) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) := by
    rw [← dualTensorHom_eq_ihomUnitTensorToIhom]
    infer_instance
  exact ⟨MonoidalClosed.exactPairingOfIsIso M⟩

end AlgebraicGeometry.Scheme.Modules
