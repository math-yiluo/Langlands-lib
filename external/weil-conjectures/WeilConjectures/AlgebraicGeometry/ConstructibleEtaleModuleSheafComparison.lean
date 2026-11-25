/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Comparing constructibility of etale module sheaves

Source: Stacks Project, Tags 095E (3), 03RU and 09XZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite-constant-value and finite-stalk definitions of constructibility agree
for module sheaves over a finite commutative ring.

Source: Stacks Project, Tags 095E (3), 03RU and 09XZ, and the global stratification
convention of `IsConstructibleEtaleModuleSheaf` and `IsConstructibleSheaf`.
(blueprint: lem-weil-pbc-constructible-etale-module-sheaf-comparison).

Proof: use the same stratification in both directions. On each stratum apply the first
equivalence of `finite_locally_constant_module_values_iff` (blueprint dependency
`lem-weil-pbc-finite-locally-constant-module-values`), which identifies the existence
of finite constant-value trivializations with `IsFiniteLocallyConstantSheaf`. -/
theorem isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ => M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ => M) F :=
  ⟨fun ⟨S, hF⟩ => ⟨S, fun k => (finite_locally_constant_module_values_iff _).1.mp (hF k)⟩,
    fun ⟨S, hF⟩ => ⟨S, fun k => (finite_locally_constant_module_values_iff _).1.mpr (hF k)⟩⟩

end AlgebraicGeometry.Scheme
