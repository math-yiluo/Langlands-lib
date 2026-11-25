/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # Conjugation of the canonical derived open/scalar comparison. -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem uniq_conjugate
    {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : M ⊣ S) (e : S ≅ R) :
    conjugateEquiv b a (a.leftAdjointUniq (b.ofNatIsoRight e)).hom = e.hom := by
  have h : a.leftAdjointUniq (b.ofNatIsoRight e) =
      (conjugateIsoEquiv b a).symm e := by
    ext X
    simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
  rw [h]
  change ((conjugateIsoEquiv b a) ((conjugateIsoEquiv b a).symm e)).hom = e.hom
  rw [Equiv.apply_symm_apply]

/-- The canonical derived open/scalar comparison is conjugate to the exact derived
restriction/scalar comparison.
Source: Stacks 0E8I, 06YY; normalization proof step 2.

Proof: The canonical comparison is defined by uniqueness of left adjoints after identifying
the two composite right adjoints with openDerivedRestrictScalarsIso. Uniqueness of left
adjoints is the inverse of the conjugation equivalence; expanding its unit and counit
formula proves this assertion. Apply conjugation and cancel this equivalence. No hypothesis
on flatness, nonzero rings or nonempty schemes is used.
(blueprint: lem-coef-etale-open-derived-conjugate). -/
theorem etaleOpenScalarDerivedConjugate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j))
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)))
      (openScalarExtension φ j).hom = (openDerivedRestrictScalarsIso φ j).hom := by
  unfold openScalarExtension
  exact uniq_conjugate _ _ _

end AlgebraicGeometry.Etale
