/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenExtensionNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenMixedTensorScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness
import all WeilConjectures.AlgebraicGeometry.ExternalRHom.EtaleScalarFlatKFlatComparison
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle

/-! # Normalization and tensor coherence of scalar change across an open immersion

Source: Stacks Tags 0E8I, 03EL, 06YY, and 0E8J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The coefficient part of the open projection formula, with all maps fixed by
adjunction and by their K-flat model normalizations.
Source: Stacks 0E8I, 03EL, 06YY, 0E8J
(blueprint: lem-coef-etale-open-scalar-coherence). -/
structure EtaleOpenScalarComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop where
  q_normalized : OpenScalarExtensionNormalization φ j (openScalarExtension φ j)
  q_unique : ∀ q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j,
    OpenScalarExtensionNormalization φ j q → q = openScalarExtension φ j
  r_normalized : OpenScalarRestrictionNormalization φ j (openScalarRestriction φ j)
  r_unique : ∀ r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j,
    OpenScalarRestrictionNormalization φ j r → r = openScalarRestriction φ j
  successive_scalar : ∀ {C : Type (u + 1)} [CommRing C] (ψ : B →+* C)
      (P : DerivedCategoryModule A U),
    (scalarExtension ψ X).map ((openScalarExtension φ j).hom.app P) ≫
        (openScalarExtension ψ j).hom.app ((scalarExtension φ U).obj P) ≫
        (derivedExtension (A := C) j).map
          ((ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app P) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((derivedExtension (A := A) j).obj P) ≫
        (openScalarExtension (ψ.comp φ) j).hom.app P
  mixed_tensor_scalar : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) ≫
        (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison U φ P ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T)

section Proofs
open CategoryTheory.Limits
universe v
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Functor.mapDerivedCategory
  derivedTensor openScalarExtension openScalarRestriction openScalarRestrictionMap
  upperStar lowerStar openImmersionLowerShriek
  scalarSheafPullbackComplexIso scalarSheafPullbackIso openScalarRestrictionZero
  ProEtale.scalarPullbackReverseEtale scalarRestrictionPullbackIso
  openDerivedRestrictScalarsIso
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  scalarExtensionRepresentative derivedOpenImmersionLowerShriekUpperStarAdjunction
  Functor.mapDerivedCategoryNatIso

private theorem cancel_square_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (R : C ⥤ D) (S : E ⥤ F) {G G' : D ⥤ F} {H H' : C ⥤ E}
    (e : G ≅ G') (f : H ≅ H') (y : R ⋙ G' ⟶ H' ⋙ S) :
    Functor.whiskerLeft R e.inv ≫
      (Functor.whiskerLeft R e.hom ≫ y ≫ Functor.whiskerRight f.inv S) ≫
        Functor.whiskerRight f.hom S = y := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simpa only [Functor.comp_obj] using Category.comp_id (y.app M)

private theorem restriction_map_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openScalarRestriction φ j).hom =
      Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).inv
          (scalarExtension φ U) ≫
        ProEtale.scalarPullbackReverseEtale φ j ≫
        Functor.whiskerLeft (scalarExtension φ X)
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom := by
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have hd := derived_square_symm φ j he
  unfold openScalarRestriction
  change openScalarRestrictionMap φ j = _
  unfold openScalarRestrictionMap openDerivedRestrictScalarsIso
  rw [hd]
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j
  have h := inverse_mate_transport a b x e e'
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
          e.inv ≫
          x ≫ Functor.whiskerRight
            e'.hom
            (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simpa only [x, scalarRestrictionPullbackIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using NatTrans.congr_app (cancel_square_transport
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ) e e'
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom).symm M
  rw [← heq] at h
  simpa only [a, b, e, e', x, ProEtale.scalarPullbackReverseEtale,
    scalarExtension, ProEtale.pbcFixedScalarExtension] using h

private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext Z
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

section
attribute [local semireducible] upperStar lowerStar
private theorem ordinary_restriction_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openScalarRestrictionZero φ j = (scalarSheafPullbackIso φ j).symm := by
  unfold openScalarRestrictionZero scalarSheafPullbackIso
  rw [uniq_eq_conjugate]
  rfl

end

private theorem restriction_complex_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarSheafPullbackComplexIso φ j).inv.app P =
      (Functor.mapHomologicalComplexCompIso
        (openScalarRestrictionZero φ j) (.up ℤ)).hom.app P := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [scalarSheafPullbackComplexIso, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, HomologicalComplex.comp_f,
    Iso.refl_hom, NatTrans.id_app]
  rw [ordinary_restriction_eq]
  exact Category.id_comp _

private theorem restriction_normalized_all
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∀ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    (openScalarRestriction φ j).hom.app (DerivedCategory.Q.obj P) ≫
        (derivedRestriction (A := B) j).map (scalarExtensionRepresentative φ X P) ≫
        (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) =
      (scalarExtension φ U).map
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionRepresentative φ U
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (openScalarRestrictionZero φ j)
            (.up ℤ)).hom.app P) := by
  intro P
  have h := reverse_normalization φ j P
  rw [geometric_rep_eq, geometric_rep_eq] at h
  rw [restriction_map_transport]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  erw [← reassoc_of%
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.naturality
      (scalarExtensionRepresentative φ X P))]
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [restriction_complex_eq]

private theorem open_conjugate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)))
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j))
      (openScalarExtension φ j).inv = (openDerivedRestrictScalarsIso φ j).inv := by
  unfold openScalarExtension
  rw [uniq_eq_conjugate]
  change (conjugateIsoEquiv _ _ ((conjugateIsoEquiv _ _).symm _)).inv = _
  rw [Equiv.apply_symm_apply]

-- Exact localization and coefficient-unit identities, proved independently here.
private theorem open_derive_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (v + 1)}
    [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
    [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{v} A₀] [HasDerivedCategory.{v} A₁] [HasDerivedCategory.{v} A₂]
    [HasDerivedCategory.{v} B₀] [HasDerivedCategory.{v} B₁] [HasDerivedCategory.{v} B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    [R₁₀.Additive] [R₂₁.Additive] [R₂₀.Additive]
    [U₁₀.Additive] [U₂₁.Additive] [U₂₀.Additive]
    [Q₀.Additive] [Q₁.Additive] [Q₂.Additive]
    [PreservesFiniteLimits R₁₀] [PreservesFiniteColimits R₁₀]
    [PreservesFiniteLimits R₂₁] [PreservesFiniteColimits R₂₁]
    [PreservesFiniteLimits R₂₀] [PreservesFiniteColimits R₂₀]
    [PreservesFiniteLimits U₁₀] [PreservesFiniteColimits U₁₀]
    [PreservesFiniteLimits U₂₁] [PreservesFiniteColimits U₂₁]
    [PreservesFiniteLimits U₂₀] [PreservesFiniteColimits U₂₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
    [PreservesFiniteLimits Q₂] [PreservesFiniteColimits Q₂]
    (e₀₁ : R₁₀ ⋙ Q₀ ≅ Q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ Q₁ ≅ Q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ Q₀ ≅ Q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = Q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (Q₂.obj M))
    (M : DerivedCategory A₂) :
    (Functor.mapDerivedCategorySquareIso e₀₂).hom.app M =
      Q₀.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso R₂₁ R₁₀) ≪≫
          Functor.mapDerivedCategoryNatIso r).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso e₀₁).hom.app (R₂₁.mapDerivedCategory.obj M) ≫
      U₁₀.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e₁₂).hom.app M) ≫
      ((Functor.mapDerivedCategoryCompIso U₂₁ U₁₀) ≪≫
        Functor.mapDerivedCategoryNatIso t).hom.app (Q₂.mapDerivedCategory.obj M) := by
  have hi (N : A₂) : e₀₂.inv.app N ≫ Q₀.map (r.inv.app N) =
      t.inv.app (Q₂.obj N) ≫ U₁₀.map (e₁₂.inv.app N) ≫ e₀₁.inv.app (R₂₁.obj N) := by
    let z := Q₀.mapIso (r.symm.app N) ≪≫ e₀₁.app (R₂₁.obj N) ≪≫
      U₁₀.mapIso (e₁₂.app N) ≪≫ t.app (Q₂.obj N)
    have hz : e₀₂.app N = z := Iso.ext (he N)
    have hh := congrArg Iso.inv hz
    dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
    rw [hh]
    simp only [Category.assoc, ← Q₀.map_comp, Iso.hom_inv_id_app, Q₀.map_id,
      Category.comp_id]
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    e₁₂.symm e₀₁.symm e₀₂.symm t.symm r.symm hi M
  apply (cancel_epi ((Functor.mapDerivedCategorySquareIso e₀₂).inv.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Category.assoc, Iso.symm_inv] at h ⊢
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

section
attribute [local semireducible] lowerStar

private theorem open_e_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map ((upperStarRestrictScalarsIsoSheaf φ f).hom.app M) =
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom) M
  have hm := underived_mate φ f
  rw [hm] at h
  simpa [lowerStarRestrictScalarsIso] using h.symm

private theorem open_e_chain {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) :
    (upperStarRestrictScalarsIsoSheaf (ψ.comp φ) f).hom.app M =
      (upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        ((upperStarRestrictScalarsIsoSheaf ψ f).hom.app M) ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((upperStar (ModuleCat.{u + 1} C) f).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [open_e_unit]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  erw [reassoc_of% (open_e_unit φ f ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M)) ≫
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIsoSheaf ψ f).hom.app M)) ≫ _
  rw [← Functor.map_comp_assoc, open_e_unit]
  ext U x
  rfl

end

private theorem right_coefficient_coherence
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategoryModule C X) :
    (openDerivedRestrictScalarsIso φ j).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ).obj K) ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).map
        ((openDerivedRestrictScalarsIso ψ j).inv.app K) ≫
      (Sheaf.derivedRestrictScalarsCompIso U.smallEtaleTopology rfl
        (f := φ) (g := ψ)).hom.app ((derivedRestriction (A := C) j).obj K) =
    (derivedRestriction (A := A) j).map
      ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
        (f := φ) (g := ψ)).hom.app K) ≫
      (openDerivedRestrictScalarsIso (ψ.comp φ) j).inv.app K := by
  have hs {R S : Type (u + 1)} [CommRing R] [CommRing S] (a : R →+* S) :
      (openDerivedRestrictScalarsIso a j).inv =
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf a j)).hom :=
    by
      unfold openDerivedRestrictScalarsIso
      exact derived_square_symm a j (Iso.ext (openRestrictScalarsIso_inv_eq a j))
  simp only [hs]
  have h := open_derive_chain
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars X.smallEtaleTopology ψ)
    (Sheaf.restrictScalars X.smallEtaleTopology (ψ.comp φ))
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars U.smallEtaleTopology ψ)
    (Sheaf.restrictScalars U.smallEtaleTopology (ψ.comp φ))
    (upperStar (ModuleCat.{u + 1} A) j) (upperStar (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} C) j)
    (upperStarRestrictScalarsIsoSheaf φ j) (upperStarRestrictScalarsIsoSheaf ψ j)
    (upperStarRestrictScalarsIsoSheaf (ψ.comp φ) j)
    (Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (Sheaf.restrictScalarsCompIso U.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (open_e_chain φ ψ j) K
  apply (cancel_epi ((derivedRestriction (A := A) j).map
    ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
      (f := φ) (g := ψ)).inv.app K))).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp,
    Sheaf.derivedRestrictScalarsCompIso] using h.symm

private theorem successive_scalar_coherence
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (P : DerivedCategoryModule A U) :
    (scalarExtension ψ X).map ((openScalarExtension φ j).hom.app P) ≫
        (openScalarExtension ψ j).hom.app ((scalarExtension φ U).obj P) ≫
        (derivedExtension (A := C) j).map
          ((ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app P) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((derivedExtension (A := A) j).obj P) ≫
        (openScalarExtension (ψ.comp φ) j).hom.app P := by
  exact (ProEtale.normalizedCocycle
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} C) j)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology (ψ.comp φ)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (ψ.comp φ)))
    (openScalarExtension φ j) (openScalarExtension ψ j) (openScalarExtension (ψ.comp φ) j)
    (ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (openDerivedRestrictScalarsIso φ j).symm (openDerivedRestrictScalarsIso ψ j).symm
    (openDerivedRestrictScalarsIso (ψ.comp φ) j).symm
    (Sheaf.derivedRestrictScalarsCompIso U.smallEtaleTopology rfl)
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl)
    (open_conjugate φ j) (open_conjugate ψ j) (open_conjugate (ψ.comp φ) j)
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _)
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _)
    (right_coefficient_coherence φ ψ j) P).symm

private theorem restriction_normalized
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    OpenScalarRestrictionNormalization φ j (openScalarRestriction φ j) := by
  intro P _
  exact restriction_normalized_all φ j P

private theorem etaleKFlat_of_flat_native
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hf : ∀ n, ObjectProperty.flat (P.X n)) : etaleKFlat X A P := by
  have h := (ExternalRHom.ringedComplex_flat_kFlat A X P hP hf).1
  change CochainComplex.IsKFlatIndependentCoefficients
    (((ExternalRHom.ringedRealization A X).mapHomologicalComplex (.up ℤ)).obj P) at h
  simpa only [ExternalRHom.realization_eq, etaleKFlat,
    Scheme.etaleSumFlatComplexRealization, Scheme.etaleSumTensorTestRealization] using h

private theorem iso_ext_flat_native
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {D : Type*} [Category D] {F G : DerivedCategoryModule A X ⥤ D}
    (a b : F ≅ G)
    (h : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ n, ObjectProperty.flat (P.X n)) →
      a.hom.app (DerivedCategory.Q.obj P) = b.hom.app (DerivedCategory.Q.obj P)) :
    a = b := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, π, hπ, hf, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  let := hπ
  apply (cancel_epi (F.map (DerivedCategory.Q.map π))).mp
  rw [a.hom.naturality, b.hom.naturality, h P hP hf]

private theorem extension_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j)
    (hq : OpenScalarExtensionNormalization φ j q)
    (hcan : OpenScalarExtensionNormalization φ j (openScalarExtension φ j)) :
    q = openScalarExtension φ j := by
  apply iso_ext_flat_native A U
  intro P hP hf
  have := scalarRepresentative_isIso φ U P hP
  apply (cancel_mono ((derivedExtension (A := B) j).map
    (scalarExtensionRepresentative φ U P))).mp
  apply (cancel_mono
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
      (((ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ)).obj P))).mp
  have hk := etaleKFlat_of_flat_native A U P hP hf
  simpa only [Category.assoc] using (hq P hk).trans (hcan P hk).symm

private theorem restriction_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j)
    (hr : OpenScalarRestrictionNormalization φ j r) :
    r = openScalarRestriction φ j := by
  apply iso_ext_flat_native A X
  intro P hP hf
  have := scalarRepresentative_isIso φ X P hP
  apply (cancel_mono ((derivedRestriction (A := B) j).map
    (scalarExtensionRepresentative φ X P))).mp
  apply (cancel_mono ((upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
    (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P))).mp
  have hk := etaleKFlat_of_flat_native A X P hP hf
  simpa only [Category.assoc] using
    (hr P hk).trans (restriction_normalized φ j P hk).symm

/-- Scalar change commutes canonically with open extension and restriction,
with the prescribed K-flat normalizations and coefficient and tensor composition laws.
Source: Stacks, Modules on Sites, Tags 0E8I and 03EL; Cohomology on Sites,
Tags 06YY and 0E8J (blueprint: lem-coef-etale-open-scalar-coherence).

Proof: Apply the ordinary open/scalar adjunctions to the balancing map on tensor
products. Uniqueness of the left adjoint identifies this map with q-zero; the
same argument for inverse image identifies it with r-zero. Apply these maps
in every degree of a complex. Transpose by the scalar adjunctions. The defining
scalar representative transposes to the localized ordinary scalar unit, and the
exact open adjunction units localize the ordinary units. Naturality of the exact
localization factors and their composition coherence therefore give the two
representative equations, in particular for every K-flat complex. Equivalently,
one can first check flat K-flat models and then resolve an arbitrary K-flat
complex by such a model; ordinary scalar extension preserves quasi-isomorphisms
between K-flat complexes, so naturality transports the same equation. On K-flat
complexes the scalar representative maps are invertible. Every derived object
has a flat K-flat resolution, transported through the constant-module
equivalence. Naturality on such a resolution and cancellation of the invertible
representative maps determine each component of q and r, hence prove the two
uniqueness assertions. In a tower A to B to C, both scalar paths act on a local
generator by ((p tensor b) tensor c) mapped to p tensor bc. The chosen scalar
composition isomorphism is the conjugate of the same restriction identity and
therefore has this formula. For the mixed square, use flat K-flat resolutions
of P and T and the uniquely normalized scalar tensor comparison. Both paths
send (p tensor b1) tensor (t tensor b2) to (p tensor t) tensor (b1*b2), followed
by extension by zero. These maps are balanced and natural; sheafification and
the direct-sum totalization preserve the equalities and their Koszul signs.
Local tensor generators generate the sheafified tensor, so the equalities
hold on the models and descend to the unbounded derived categories. No
flatness of B over A or quasi-compactness of the open immersion is used. -/
theorem etaleOpenScalarComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenScalarComparisons φ j := by
  refine {
    q_normalized := etaleOpenExtensionNormalization φ j
    q_unique := fun q hq ↦ extension_unique φ j q hq (etaleOpenExtensionNormalization φ j)
    r_normalized := restriction_normalized φ j
    r_unique := restriction_unique φ j
    successive_scalar := fun ψ P ↦ successive_scalar_coherence φ ψ j P
    mixed_tensor_scalar := etaleOpenMixedTensorScalar φ j }

end Proofs

end AlgebraicGeometry.Etale
