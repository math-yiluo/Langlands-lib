/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
/-!
# Finite-coefficient comparison in the intrinsic constant-ring presentation

The existing finite-coefficient comparison uses modules over sheafified continuous
functions. Intrinsic constructibility uses modules over the constant commutative ring
sheaf. The canonical associated-module-sheaf construction below supplies this second
presentation of the same exact inverse image, with constant scalar action fixed by the
sheafification unit. It does not choose an abstract equivalence or a new inverse image.

## References

* Stacks, Tags 099R and 00YV
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant-scalar unit into the underlying ring of the commutative constant sheaf. -/
noncomputable def finiteCoefficientIntrinsicScalarMap (T : Scheme.{u})
    (B : Type u) [CommRing B] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)) ⟶
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing T B)).obj :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private noncomputable def intrinsicModulePresheafFullyFaithful
    (C : Type (u + 1)) [Category.{u} C] (Λ : Type (u + 1)) [Ring Λ] :
    (finiteCoefficientModulePresheaf C Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private theorem intrinsicRealization_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  have : (finiteCoefficientModulePresheaf C Λ).Full :=
    (intrinsicModulePresheafFullyFaithful C Λ).full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful :=
    (intrinsicModulePresheafFullyFaithful C Λ).faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    refine ⟨F', ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

/-- Local injectivity for the canonical associated-module-sheaf construction. -/
noncomputable instance finiteCoefficientIntrinsicScalarMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T)
      (finiteCoefficientIntrinsicScalarMap T B) :=
  (Scheme.proEtaleConstantRingUnit_locallyBijective T B).1

/-- Local surjectivity for the canonical associated-module-sheaf construction. -/
noncomputable instance finiteCoefficientIntrinsicScalarMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (finiteCoefficientIntrinsicScalarMap T B) :=
  (Scheme.proEtaleConstantRingUnit_locallyBijective T B).2

/-- Canonical realization over the constant commutative coefficient sheaf: keep the
fixed-scalar module presheaf and sheafify it along the constant-scalar unit. -/
noncomputable def finiteCoefficientIntrinsicRealization :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B) ⋙
    PresheafOfModules.sheafification (finiteCoefficientIntrinsicScalarMap T B)

set_option linter.unusedSectionVars false in
/-- This is an additive exact equivalence of the two presentations of module sheaves. -/
theorem finiteCoefficientIntrinsicRealization_exact :
    (finiteCoefficientIntrinsicRealization T B).IsEquivalence ∧
    (finiteCoefficientIntrinsicRealization T B).Additive ∧
    PreservesFiniteLimits (finiteCoefficientIntrinsicRealization T B) ∧
    PreservesFiniteColimits (finiteCoefficientIntrinsicRealization T B) := by
  have : (finiteCoefficientIntrinsicRealization T B).IsEquivalence :=
    intrinsicRealization_isEquivalence (Scheme.ProEt.topology T) (ULift.{u + 1, u} B)
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing T B)) (finiteCoefficientIntrinsicScalarMap T B)
  exact ⟨this, Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientIntrinsicRealization_additive :
    (finiteCoefficientIntrinsicRealization T B).Additive :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.1

/-- Left exactness of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientIntrinsicRealization_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientIntrinsicRealization T B) :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.2.1

/-- Right exactness of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientIntrinsicRealization_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientIntrinsicRealization T B) :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.2.2

/-- The specified comparison inverse image, expressed over the intrinsic constant ring. -/
noncomputable def finiteCoefficientIntrinsicComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
    finiteCoefficientIntrinsicRealization T B

/-- The intrinsic comparison is additive. -/
noncomputable instance finiteCoefficientIntrinsicComparison_additive :
    (finiteCoefficientIntrinsicComparison T B).Additive :=
  inferInstanceAs (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
    finiteCoefficientIntrinsicRealization T B).Additive

/-- The intrinsic comparison is left exact. -/
noncomputable instance finiteCoefficientIntrinsicComparison_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientIntrinsicComparison T B) :=
  inferInstanceAs (PreservesFiniteLimits
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
      finiteCoefficientIntrinsicRealization T B))

/-- The intrinsic comparison is right exact. -/
noncomputable instance finiteCoefficientIntrinsicComparison_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientIntrinsicComparison T B) :=
  inferInstanceAs (PreservesFiniteColimits
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
      finiteCoefficientIntrinsicRealization T B))

/-- The exact inverse image on derived categories, in the coefficient presentation of
intrinsic constructibility, obtained by applying the specified comparison termwise. -/
noncomputable def finiteCoefficientIntrinsicDerivedComparison :
    FiniteCoefficientEtaleDerivedCategory T (ULift.{u + 1, u} B) ⥤
      Scheme.proEtaleDerivedCategory T B :=
  (finiteCoefficientIntrinsicComparison T B).mapDerivedCategory

end AlgebraicGeometry.ProEtale
