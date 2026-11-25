/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Algebra.Homology.ResidueKernelLocalizedCokernelTransport

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- Localizing a cokernel agrees with the cokernel of scalar extension.

Source: Mathlib.Algebra.Module.LocalizedModule.Submodule,
`LinearMap.localized'_range_eq_range_localizedMap` and
`IsLocalizedModule.toLocalizedQuotient'`; localization/scalar-extension comparison
from Mathlib.RingTheory.Localization.BaseChange.
Proof: The maps y ↦ 1 ⊗ y exhibit scalar extensions as localized modules.
Localization carries the range of f to the range of its scalar extension.
The quotient by that localized range is a localization of Y/range f, by the
universal property of localization of a quotient. Uniqueness of localized modules
identifies it with LocalizedModule, and this equivalence is linear over R_p.
Explicitly, set A = R_p, S = p.primeCompl, and iY(y) = 1 ⊗ y. The submodule
(range f).localized' A S iY equals the range of the base-changed f. Apply
IsLocalizedModule.linearEquiv to the canonical localization map of Y/range f
and (range f).toLocalizedQuotient' A S iY, then extend its scalars to A and
transport the quotient along the range equality. Finally identify the canonical
tensor-product action with the action used by ModuleCat.extendScalars; these
actions agree by algebraMap_smul. This argument needs no finiteness assumptions.
(blueprint: new-residue-kernel-localized-cokernel) -/
theorem residue_kernel_localized_cokernel
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Nonempty (LocalizedModule 𝔭.primeCompl (Y ⧸ LinearMap.range f.hom)
      ≃ₗ[Localization.AtPrime 𝔭]
        (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
          ⧸ LinearMap.range ((ModuleCat.extendScalars
            (algebraMap R (Localization.AtPrime 𝔭))).map f).hom)) := by
  obtain ⟨e⟩ := localized_range_quotient_extendScalars R X Y f 𝔭
  exact ⟨(localizedQuotientEquiv 𝔭.primeCompl (LinearMap.range f.hom)).symm.trans e⟩

end ModuleCat
