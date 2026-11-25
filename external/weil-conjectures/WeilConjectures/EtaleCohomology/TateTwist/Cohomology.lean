/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Cohomology with Tate twisted finite coefficients

Let `Λ` be a finite coefficient ring, in the blueprint `A_{E,n} = 𝒪_E / ϖ_Eⁿ`, and `Y` a scheme
on which the characteristic of `Λ` is invertible. Following blueprint
`def-weil-ordinary-compact-cohomology`, the cohomology with coefficients in the Tate twist
`Λ(m)` is the cohomology of the twisting object `Λ_Y(m) = Λ_Y ⊗ᴸ Λ(m)_Y`
(`AlgebraicGeometry.Etale.tateTwistObject`, blueprint `definition-tate-twists`):

`Hⁱ(Y, Λ(m)) = Hⁱ(RΓ(Y, Λ_Y(m)))` (`AlgebraicGeometry.Etale.cohomologyTateTwist`), and, along
a morphism `a : Y ⟶ s` admitting a compactification,
`Hⁱ_c(Y, Λ(m)) = Hⁱ(RΓ(s, Ra_! Λ_Y(m)))`
(`AlgebraicGeometry.Etale.compactlySupportedCohomologyTateTwist`).

The untwisted cohomology of a complex is `AlgebraicGeometry.Etale.cohomology` and
`AlgebraicGeometry.Etale.compactlySupportedCohomology`; for `m = 0` the twisting object is the
constant complex `Λ_Y` (`AlgebraicGeometry.Etale.tateTwistObjectZeroIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)]

/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, finite stage `Λ = A_{E,n}`, with a Tate twist.

The cohomology `Hⁱ(Y, Λ(m)) = Hⁱ(RΓ(Y, Λ_Y(m)))` of a scheme `Y` with coefficients in the Tate
twist `Λ(m)`: the étale cohomology (`AlgebraicGeometry.Etale.cohomology`) of the twisting object
`Λ_Y(m)` (`AlgebraicGeometry.Etale.tateTwistObject`). The exponent of `Λ` is assumed
invertible on `Y`: otherwise `AlgebraicGeometry.Etale.tateTwistObject` is the untwisted
`Λ_Y`. -/
noncomputable def cohomologyTateTwist (Y : Scheme.{u}) [HasInvertibleExponent Λ Y] (m i : ℤ) :
    ModuleCat.{u + 1} Λ :=
  (cohomology (ModuleCat.{u + 1} Λ) Y i).obj (tateTwistObject Λ Y m)

/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, finite stage `Λ = A_{E,n}`, with a Tate twist.

The compactly supported cohomology `Hⁱ_c(Y, Λ(m)) = Hⁱ(RΓ(s, Ra_! Λ_Y(m)))` along a morphism
`a : Y ⟶ s` admitting a compactification: the compactly supported cohomology
(`AlgebraicGeometry.Etale.compactlySupportedCohomology`) of the twisting object `Λ_Y(m)`, for
the exponent of `Λ` invertible on `Y`. -/
noncomputable def compactlySupportedCohomologyTateTwist {Y s : Scheme.{u}} (a : Y ⟶ s)
    [HasCompactification a] [HasInvertibleExponent Λ Y] (m i : ℤ) : ModuleCat.{u + 1} Λ :=
  (compactlySupportedCohomology (ModuleCat.{u + 1} Λ) a i).obj (tateTwistObject Λ Y m)

end AlgebraicGeometry.Etale
