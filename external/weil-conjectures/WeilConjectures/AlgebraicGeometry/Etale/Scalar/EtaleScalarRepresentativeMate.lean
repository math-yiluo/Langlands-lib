/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # The scalar representative as an adjunction mate. -/

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

/-- The fixed scalar cochain representative is the inverse mate of the exact restriction
localization factor.
Source: Stacks 03EK, 06YY; normalization proof step 1.

Proof: In each degree the cochain scalar unit is the ordinary scalar unit, so it equals
scalarRepresentativeUnit. The unit identity for inverse mates therefore agrees with the
published unit transpose of scalarExtensionRepresentative. Injectivity of the derived
scalar adjunction's hom equivalence identifies the two maps. This holds for all cochain
complexes, without flatness and also for zero rings.
(blueprint: lem-coef-etale-scalar-representative-mate). -/
theorem etaleScalarRepresentativeMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((mateEquiv
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))).symm
      (TwoSquare.mk _ _ _ _
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv)).app P =
      scalarExtensionRepresentative φ T P := by
  let a := (ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  have hu : a.unit.app P = scalarRepresentativeUnit φ T P := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [a, scalarRepresentativeUnit, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Adjunction.mapHomologicalComplex_unit_app_f]
    erw [Category.id_comp, Category.comp_id]
  have h := unit_mateEquiv_symm a b
    (TwoSquare.mk _ _ _ _
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv) P
  rw [hu] at h
  apply (b.homEquiv _ _).injective
  exact h.symm.trans (scalarExtensionRepresentative_unit_public φ T P).symm

end AlgebraicGeometry.Etale
