/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-! # Lattices in lisse `E`-sheaves

Let `E / ℚ_ℓ` be finite and let `L` be a lisse `E_X`-module on `X_proét`. A lattice in `L`
is a lisse `𝒪_{E,X}`-submodule `M ⊆ L` with `M[1/ℓ] = L`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- A *lattice* in an `E_X`-module `L`: a lisse `𝒪_{E,X}`-module `M` together with an
`𝒪_{E,X}`-linear monomorphism `ι : M ⟶ L`, where `L` is regarded as an `𝒪_{E,X}`-module by
restriction of scalars, such that `M[1/ℓ] = L`, i.e. the `E_X`-linear map
`E_X ⊗_{𝒪_{E,X}} M ⟶ L` adjoint to `ι` is an isomorphism. -/
structure IsLattice {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)}
    (ι : M ⟶ (Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj L) : Prop where
  /-- The submodule is a lisse `𝒪_{E,X}`-module. -/
  isLisse : IsLisseCoefficientModule (integralCoeff ℓ E) M
  /-- The map `M ⟶ L` is injective. -/
  mono : Mono ι
  /-- Inverting `ℓ` recovers `L`: `E_X ⊗_{𝒪_{E,X}} M ⟶ L` is an isomorphism. -/
  isIso_extendScalars :
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap ℓ E) X)).homEquiv
      M L).symm ι)

end AlgebraicGeometry.ProEtale.CondensedRing
