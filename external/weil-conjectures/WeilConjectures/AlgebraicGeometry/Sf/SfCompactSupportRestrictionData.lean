/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Normalized finite coefficient comparison data

All comparisons are normalized before choosing them: realization preserves sections,
extension by zero uses the adjunction unit, and derived direct image uses its
K-injective comparison. Thus the compactification and coefficient map enter the actual
functors and maps.

## References

* Bhatt--Scholze, Sections 6.5 and 6.7
* Stacks Tags 00YV and 03DA
* Stacks Tags 0D6E and 0D6J
* Bhatt--Scholze, Lemma 6.7.7
* Stacks Tags 03DI and 0D6E
* Stacks Tag 015F
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- Fixed scalar restriction on the pro-etale site. -/
noncomputable abbrev sfFixedRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  sheafCompose (ProEt.topology T) (ModuleCat.restrictScalars.{u + 1} φ.ulift)

/-- Realization commutes with restriction of scalars, for a general pair of locally bijective
constant-scalar maps `α`, `α'` and ring-sheaf map `δ` compatible with `φ`: there is a unique
natural isomorphism which is the identity on sections. -/
private theorem realization_restrict_existsUnique {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {Λ Λ' : Type (u + 1)} [Ring Λ] [Ring Λ']
    (R R' : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    (α' : (Functor.const Cᵒᵖ).obj (RingCat.of Λ') ⟶ R'.obj)
    (φ : Λ →+* Λ') (δ : R ⟶ R')
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J α'] [Presheaf.IsLocallySurjective J α']
    [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (h : α ≫ δ.hom = (Functor.const Cᵒᵖ).map (RingCat.ofHom φ) ≫ α') :
    ∃! e : (sheafToPresheaf J (ModuleCat.{u + 1} Λ') ⋙
          ProEtale.finiteCoefficientModulePresheaf C Λ' ⋙
          PresheafOfModules.sheafification.{u + 1} α') ⋙
          SheafOfModules.restrictScalars.{u + 1} δ ≅
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙
          (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙ ProEtale.finiteCoefficientModulePresheaf C Λ ⋙
            PresheafOfModules.sheafification.{u + 1} α),
      ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ')) (U : Cᵒᵖ)
        (x : ((PresheafOfModules.sheafification.{u + 1} α').obj
          ((ProEtale.finiteCoefficientModulePresheaf C Λ').obj M.obj)).val.obj U),
        (e.hom.app M).val.app U x = x := by
  let P' : Sheaf J (ModuleCat.{u + 1} Λ') → _root_.PresheafOfModules.{u + 1}
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ')) :=
    fun M ↦ (ProEtale.finiteCoefficientModulePresheaf C Λ').obj M.obj
  let g (M : Sheaf J (ModuleCat.{u + 1} Λ')) :
      (ProEtale.finiteCoefficientModulePresheaf C Λ).obj
          ((sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).obj M).obj ⟶
        (PresheafOfModules.restrictScalars α).obj ((SheafOfModules.forget _).obj
          ((SheafOfModules.restrictScalars δ).obj
            ((PresheafOfModules.sheafification.{u + 1} α').obj (P' M)))) :=
    PresheafOfModules.homMk (toSheafify J (P' M).presheaf) (by
      intro U r m
      have h1 := (((PresheafOfModules.sheafificationAdjunction α').unit.app
        (P' M)).app U).hom.map_smul (φ r) m
      have h2 : δ.hom.app U (α.app U r) = α'.app U (φ r) :=
        ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) h) r
      change _ = (δ.hom.app U (α.app U r) : R'.obj.obj U) •
        (show ((PresheafOfModules.sheafification.{u + 1} α').obj (P' M)).val.obj U from
          (toSheafify J (P' M).presheaf).app U m)
      rw [h2]
      exact h1)
  let f (M : Sheaf J (ModuleCat.{u + 1} Λ')) :=
    (PresheafOfModules.sheafificationHomEquiv α).symm (g M)
  have hf (M : Sheaf J (ModuleCat.{u + 1} Λ')) :
      (SheafOfModules.toSheaf _).map (f M) = 𝟙 _ := by
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv_id _).symm
  have hf' (M : Sheaf J (ModuleCat.{u + 1} Λ')) (U : Cᵒᵖ)
      (y : ((PresheafOfModules.sheafification.{u + 1} α').obj (P' M)).val.obj U) :
      (f M).val.app U y = y :=
    congrArg (fun k ↦ k.hom.app U y) (hf M)
  have : ∀ M, IsIso (f M) := fun M ↦ by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _), hf M]
    infer_instance
  let e₀ : sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙ ProEtale.finiteCoefficientModulePresheaf C Λ ⋙
          PresheafOfModules.sheafification.{u + 1} α) ≅
      (sheafToPresheaf J (ModuleCat.{u + 1} Λ') ⋙ ProEtale.finiteCoefficientModulePresheaf C Λ' ⋙
          PresheafOfModules.sheafification.{u + 1} α') ⋙
        SheafOfModules.restrictScalars.{u + 1} δ :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (fun {M N} a ↦ by
      apply (SheafOfModules.toSheaf _).map_injective
      simp only [Functor.map_comp, asIso_hom, hf]
      rfl)
  have he : ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ')) (U : Cᵒᵖ)
      (x : ((PresheafOfModules.sheafification.{u + 1} α').obj (P' M)).val.obj U),
      (e₀.symm.hom.app M).val.app U x = x := fun M U x ↦ by
    refine (hf' M U ((inv (f M)).val.app U x)).symm.trans ?_
    change ((inv (f M) ≫ f M).val.app U) x = x
    rw [IsIso.inv_hom_id]
    rfl
  refine ⟨e₀.symm, he, fun e' he' ↦ ?_⟩
  apply Iso.ext
  ext M U x
  exact (he' M U x).trans (he M U x).symm


/-- Realization commutes with scalar restriction by the identity on the sheafified
underlying abelian presheaf. -/
theorem sfRealizationRestriction_existsUnique (T : Scheme.{u}) (φ : A →+* B) :
    ∃! e : (sfIntrinsicModuleEquivalence T B).functor ⋙
        proEtaleCoefficientRestrictScalars T φ ≅
      sfFixedRestriction T φ ⋙ (sfIntrinsicModuleEquivalence T A).functor,
      ∀ (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (U : T.ProEtᵒᵖ)
        (x : (((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj U)),
        (e.hom.app M).val.app U x = x := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := φ.ulift
  let δ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ'))
  apply realization_restrict_existsUnique (ProEt.topology T) _ _
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
    (ProEtale.finiteCoefficientIntrinsicScalarMap T B) φ' δ
  exact (congrArg (fun k ↦ Functor.whiskerRight k
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ')))).symm

/-- The sectionwise normalized realization comparison. -/
noncomputable def sfRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose

/-- The inverse-equivalence coefficient square, obtained by unit and counit from the
normalized realization square. -/
noncomputable def sfInverseRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse ≅
      (sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T B).counitIso.symm
      (proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T B).inverse
      (Functor.isoWhiskerRight (sfRealizationRestriction T φ)
        (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ)
      (sfIntrinsicModuleEquivalence T A).unitIso.symm

/-- Fixed-scalar extension by zero commutes with restriction: both sides are left
adjoint to the same objectwise composite of open restriction and coextension.
The left-adjoint uniqueness map is normalized by the adjunction units. -/
noncomputable def sfFixedOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    sfFixedRestriction X φ ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
        sfFixedRestriction Z φ :=
  ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ.ulift).comp
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).leftAdjointUniq
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ.ulift))

/-- The intrinsic extension-by-zero coefficient square, transported by the canonical
realization equivalences. -/
noncomputable def sfOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars X φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction X φ)
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X B).inverse
      (Functor.isoWhiskerRight (sfFixedOpenRestriction j φ)
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence X B).inverse ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction Z φ).symm

/-- Derived direct-image coefficient comparison selected with the full K-injective
normalization of the recorded direct-image theorem. That normalization determines the
natural isomorphism on every K-injective representative and hence after localization. -/
noncomputable def sfDerivedImageRestriction {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory ⋙
        proEtaleConstantDerivedDirectImage g A ≅
      proEtaleConstantDerivedDirectImage g B ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  (proEtaleDerivedDirectImage_restrictScalars g φ).choose

/-- The specified compact-support comparison is the extension-by-zero square followed
by the direct-image square, with no change of compactification. -/
noncomputable def sfCompactSupportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory ⋙
        sfAmbientCompactSupportCandidate A c ≅
      sfAmbientCompactSupportCandidate B c ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ))
      (proEtaleConstantDerivedDirectImage c.g A) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
      (sfDerivedImageRestriction c.g φ)

/-- The normalized scalar-restriction composition map, using the shared sectionwise
identity comparison for commutative ring sheaves. -/
noncomputable def sfCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :
    proEtaleCoefficientRestrictScalars T ψ ⋙ proEtaleCoefficientRestrictScalars T φ ≅
      proEtaleCoefficientRestrictScalars T (ψ.comp φ) :=
  pbcRestrictComp
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ψ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ψ.comp φ).ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm

/-- The termwise derived scalar composition map. -/
noncomputable def sfDerivedCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (sfCoefficientRestrictionComp T φ ψ)

end AlgebraicGeometry.Scheme
