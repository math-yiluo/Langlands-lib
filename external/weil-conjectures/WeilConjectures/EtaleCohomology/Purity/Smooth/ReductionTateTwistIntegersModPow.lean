/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import WeilConjectures.NumberTheory.Padics.IntegersModPowTransition
public import WeilConjectures.TateTwist.FiniteRootsOfUnity

/-!
# The Tate shift datum of the reduction `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`

The transition map `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ` is surjective with principal kernel
(`PadicAlgCl.ker_integersModPowULiftTransition`), so the derived extension of scalars along it is
a change of coefficients, and the identifications
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` induced by `μ_{ℓ^{n+1}} ⊗ 𝒪_E ⧸ ℓⁿ ≅ μ_{ℓⁿ} ⊗ 𝒪_E ⧸ ℓⁿ` form its
Tate shift datum (`AlgebraicGeometry.Etale.integersModPowReductionTateShiftData`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

open ProEtale.CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- Blueprint `proposition-compatibility-purity-change-coefficients`

The Tate shift datum of the derived extension of scalars along the reduction
`𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`, induced by `μ_{ℓ^{n+1}} ⊗ 𝒪_E ⧸ ℓⁿ ≅ μ_{ℓⁿ} ⊗ 𝒪_E ⧸ ℓⁿ`
(`AlgebraicGeometry.Etale.reductionTateShiftData`). -/
noncomputable def integersModPowReductionTateShiftData :
    DerivedExtendScalarsTateShiftData (integersModPowCoeff.{u} ℓ E (n + 1))
      (integersModPowCoeff.{u} ℓ E n) (integersModPowULiftTransition_surjective.{u + 1} ℓ E n)
      (ker_integersModPowULiftTransition.{u + 1} ℓ E n) :=
  reductionTateShiftData _ _

end AlgebraicGeometry.Etale
