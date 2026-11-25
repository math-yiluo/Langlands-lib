/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Canonical unit and reassociation for quotient scalar extensions

The definitions are relocated verbatim from NormalizedEtaleOriginWitnesses.

## References

* Stacks Tags 06YY and 09B1, coefficient refinement of the compatible-origin argument
* Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
* Stacks 06YY and 09B1, coefficient refinement
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Canonical identity restriction on sheaves, given by identity section maps. -/
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism. -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- Direct quotient scalar extension, in the fixed-ring presentation. -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (m n : ℕ) (h : n ≤ m) :=
  pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n h)

end AlgebraicGeometry.ProEtale
