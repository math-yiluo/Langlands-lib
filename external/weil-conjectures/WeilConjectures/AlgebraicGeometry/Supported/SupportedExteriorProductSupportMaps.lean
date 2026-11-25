/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedSupportTriangle
import WeilConjectures.AlgebraicGeometry.Supported.SupportedTensorComparisonNaturality
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientDerivedOpenMate
/-! # Supported exterior products and maps of supports -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
private noncomputable def coefficientMap (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (r : supportedEtaleSections A T b.openComplement ⟶
      supportedEtaleSections A T c.openComplement) :
    supportedCoefficients A c ⟶ supportedCoefficients A b :=
  (conjugateEquiv (supportedCoefficientAdjunction A b)
    (supportedCoefficientAdjunction A c)).symm r

section SupportMaps
variable (A : Type (u + 1)) [CommRing A]
    {S X Y B B' D D' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (b' : B' ⟶ X) (d : D ⟶ Y) (d' : D' ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion b']
    [IsClosedImmersion d] [IsClosedImmersion d']
    (r₁ : supportedEtaleSections A X b.openComplement ⟶
      supportedEtaleSections A X b'.openComplement)
    (r₂ : supportedEtaleSections A Y d.openComplement ⟶
      supportedEtaleSections A Y d'.openComplement)
    (r₀ : supportedEtaleSections A (pullback f g)
        (supportedProductImmersion f g b d).openComplement ⟶
      supportedEtaleSections A (pullback f g)
        (supportedProductImmersion f g b' d').openComplement)
    (hr₁ : r₁ ≫ supportedEtaleSectionsι A X b'.openComplement =
      supportedEtaleSectionsι A X b.openComplement)
    (hr₂ : r₂ ≫ supportedEtaleSectionsι A Y d'.openComplement =
      supportedEtaleSectionsι A Y d.openComplement)
    (hr₀ : r₀ ≫ supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b' d').openComplement =
      supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b d).openComplement)

include hr₁ hr₂ hr₀

attribute [local irreducible] derivedTensor

end SupportMaps

end AlgebraicGeometry.Etale
