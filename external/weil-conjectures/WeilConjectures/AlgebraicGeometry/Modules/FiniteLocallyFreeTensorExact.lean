/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree

/-!
# Exactness of tensoring by a finite locally free module

## References

* Stacks Project, Tags 01C6, 01CB, 01AG and 05NE
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring on the left by a finite locally free module is exact: it preserves finite
limits and finite colimits, equivalently short exact sequences in the abelian module category.
The local finite ranks may vary across the scheme. -/
theorem finiteLocallyFree_tensorLeft_exact {X : Scheme.{u}} (P : X.Modules)
    [P.IsFiniteLocallyFree] :
    PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P) := by
  -- Finite locally free biduality identifies tensoring by P with internal Hom from its dual.
  have := IsFiniteLocallyFree.dual P
  have := SheafOfModules.isIso_bidual (R := X.sheaf) P
  let e : tensorLeft P ≅ ihom (dual P) :=
    (tensoringLeft X.Modules).mapIso (asIso (SheafOfModules.bidual (R := X.sheaf) P)) ≪≫
      NatIso.ofComponents (fun N ↦ asIso (dualTensorHom (dual P) N)) fun g ↦
        dualTensorHom_naturality_right (dual P) g
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  exact ⟨preservesFiniteLimits_of_natIso e.symm, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
