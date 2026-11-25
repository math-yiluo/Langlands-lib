/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedScalarSymmetry

/-! # Normalization of one side of the ordered scalar projection square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar openImmersionLowerShriek
  derivedTensor derivedTensorSymmetry derivedOpenImmersionLowerShriekProjectionIso
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.openIso
  leftDerivedUpperStarIsoMapDerivedCategory

private lemma conj_transport {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₁') (f : R₂ ≅ R₂')
    (α : L₂ ⟶ L₁) :
    conjugateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight f) α =
      e.inv ≫ conjugateEquiv a b α ≫ f.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← f.hom.naturality_assoc, ← f.hom.naturality_assoc, ← f.hom.naturality]
  rw [← R₂.map_comp_assoc, ← α.naturality, R₂.map_comp_assoc]
  rw [← b.unit_naturality_assoc]

private lemma comp_transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ E} {S S' : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (e : R ≅ R') (f : S ≅ S') :
    (a.ofNatIsoRight e).comp (b.ofNatIsoRight f) =
      (a.comp b).ofNatIsoRight
        (isoWhiskerLeft S e ≪≫ isoWhiskerRight f R') := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [← e.hom.naturality_assoc]

private lemma transport_refl {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    adj.ofNatIsoRight (Iso.refl G) = adj := by
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoRight_unit]

private lemma conjugate_comp_transport
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ F} {S : F ⥤ D}
    {N : C ⥤ E} {T : E ⥤ C} {P : E ⥤ F} {Q Q' : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) (d : P ⊣ Q)
    (e : R ≅ R') (f : Q ≅ Q') (α : N ⋙ P ⟶ L ⋙ M)
    (β : S ⋙ R ⟶ Q ⋙ T)
    (h : conjugateEquiv (a.comp b) (c.comp d) α = β) :
    conjugateEquiv ((a.ofNatIsoRight e).comp b) (c.comp (d.ofNatIsoRight f)) α =
      Functor.whiskerLeft S e.inv ≫ β ≫ Functor.whiskerRight f.hom T := by
  have h₁ := comp_transport a b e (Iso.refl _)
  have h₂ := comp_transport c d (Iso.refl _) f
  rw [transport_refl] at h₁ h₂
  rw [h₁, h₂, conj_transport, h]
  ext X
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp]

private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext Z
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem open_comparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ExceptionalCoefficients.openIso φ j = openScalarExtension φ j := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let c := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let d := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let f := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j
  have hq : conjugateEquiv (a.comp b) (c.comp d) (openScalarExtension φ j).inv =
      (openDerivedRestrictScalarsIso φ j).inv := by
    unfold openScalarExtension
    rw [uniq_eq_conjugate]
    change (conjugateIsoEquiv _ _ ((conjugateIsoEquiv _ _).symm _)).inv = _
    rw [Equiv.apply_symm_apply]
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have hs := derived_square_symm φ j he
  have h := conjugate_comp_transport a b c d e.symm f.symm
    (openScalarExtension φ j).inv (openDerivedRestrictScalarsIso φ j).inv hq
  have hsq : conjugateEquiv ((a.ofNatIsoRight e.symm).comp b)
      (c.comp (d.ofNatIsoRight f.symm)) (openScalarExtension φ j).inv =
        (scalarRestrictionPullbackIso φ j).hom := by
    rw [h]
    dsimp only [openDerivedRestrictScalarsIso]
    rw [hs]
    rfl
  apply Iso.ext_inv
  unfold ExceptionalCoefficients.openIso
  apply (conjugateEquiv ((a.ofNatIsoRight e.symm).comp b)
    (c.comp (d.ofNatIsoRight f.symm))).injective
  change conjugateEquiv _ _ ((conjugateEquiv _ _).symm
    (scalarRestrictionPullbackIso φ j).hom) = _
  rw [Equiv.apply_symm_apply]
  exact hsq.symm

private theorem tensor_comparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (Z : Scheme.{u}) (K L : DerivedCategoryModule A Z) :
    etaleHomTensorComparison Z φ K L =
      ((ExceptionalCoefficients.tensorIso φ Z).app (K, L)).symm := by
  let δ := ExceptionalCoefficients.tensorIso φ Z
  have hδ : ExceptionalCoefficients.TensorNormalization φ Z δ := by
    have he : δ = (ExceptionalCoefficients.tensorIso_existsUnique φ Z).choose := by
      unfold δ ExceptionalCoefficients.tensorIso
      exact eq_of_heq
        (ExceptionalCoefficients.siteTensorIso_existsUnique φ Z).choose_spec.1
    exact he.symm ▸ (ExceptionalCoefficients.tensorIso_existsUnique φ Z).choose_spec.1
  have hc : IsEtaleHomTensorCanonical Z φ (fun K L ↦ (δ.app (K, L)).symm) := by
    refine ⟨ExceptionalCoefficients.productIso_natural₁ _ _ _ δ,
      ExceptionalCoefficients.productIso_natural₂ _ _ _ δ, ?_⟩
    exact ExceptionalCoefficients.site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) Z (ProEtale.etaleSheafExtendScalars φ Z)
      (scalarExtension φ Z) (scalarExtensionRepresentative φ Z) δ hδ
  have hh := (etaleHomTensorComparison_existsUnique Z φ).choose_spec.2 _ hc
  exact (congrFun (congrFun hh K) L).symm

private theorem symmetry_inv
    (R : Type (u + 1)) [CommRing R] (Z : Scheme.{u})
    (K L : DerivedCategoryModule R Z) :
    ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Z).inv.app K).app L =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Z).hom.app L).app K := by
  apply (cancel_epi
    (((derivedTensorSymmetry (ModuleCat.{u + 1} R) Z).hom.app K).app L)).1
  rw [Iso.hom_inv_id_app_app, derivedTensorSymmetry_involutive]

/-- Normalize the source-side scalar transport and the exact open projection.
Source: Stacks 0E8I, 0GL6 and 07A4; the source normalization in the local open square
(blueprint: lem-pur-ordered-scalar-source-normalization).

Proof: the two adjacent signed symmetries inside extension by zero are inverse,
by involutivity of the Koszul swap. The exact/left-derived pullback comparison
then converts canonicalGammaExact to the canonical open projection, which cancels
its inverse. Move the open comparison past the ambient inverse symmetry by
naturality. The open comparison and openScalarExtension have the same unit
transpose and hence cancel. Finally tensorIso is the inverse normalized scalar
tensorator. On flat K-flat representatives the scalar tensorator commutes with the
signed swap: both routes send a homogeneous tensor of bidegree (p,q) to its swap
with sign (-1)^(p*q), and the scalar has degree zero. Equality on tensor generators
gives equality of chain maps; localization and naturality of resolutions extend it
to all inputs. This gives the image of the ambient inverse symmetry displayed here,
including empty opens, zero objects and zero coefficient rings. -/
theorem etaleOrderedScalar_sourceNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule A Z) (M : DerivedCategoryModule A X) :
    (((ExceptionalCoefficients.tensorIso φ Z).hom.app
        (T, (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Z).obj
        ((scalarExtension φ Z).obj T)).map
          ((ExceptionalCoefficients.openIso φ j).hom.app M) ≫
      (((derivedTensorSymmetry (ModuleCat.{u + 1} B) Z).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
      ((scalarExtension φ X).obj M))).app
        ((scalarExtension φ Z).obj T) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} B) j).inv.app
        ((scalarExtension φ X).obj M)).app ((scalarExtension φ Z).obj T) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app ((scalarExtension φ X).obj M)).app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj ((scalarExtension φ
      Z).obj T))))) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M))) ≫
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
          ((scalarExtension φ Z).obj T)))) ≫
    (canonicalGammaExact (ModuleCat.{u + 1} B) j
          ((scalarExtension φ X).obj M) ((scalarExtension φ Z).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) Z).map
          ((openScalarExtension φ j).inv.app M)).app ((scalarExtension φ Z).obj T) ≫
        (etaleHomTensorComparison Z φ ((derivedExtension j).obj M) T).hom) =
    (scalarExtension φ Z).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)).app T)
      := by
  let U := (scalarExtension φ Z).obj T
  let N := (scalarExtension φ X).obj M
  let H := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
  let L := (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj U
  have hsw := derivedTensorSymmetry_involutive B X N L
  have hcancel :
      J.map (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app N).app L) ≫
        J.map (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app L).app N) =
          𝟙 _ := by
    rw [← J.map_comp, hsw, J.map_id]
  have hproj :
      J.map (((derivedTensor (ModuleCat.{u + 1} B) X).obj N).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app U)) ≫
        canonicalGammaExact (ModuleCat.{u + 1} B) j N U =
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} B) j).hom.app N).app
        U := by
    rw [canonicalGammaExact, ← J.map_comp_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, J.map_id,
      Category.id_comp,
      derivedOpenImmersionLowerShriekProjectionIso_hom]
  rw [open_comparison_eq, tensor_comparison_eq, symmetry_inv, symmetry_inv]
  simp only [Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% hcancel, reassoc_of% hproj,
    Iso.inv_hom_id_app_app_assoc]
  rw [reassoc_of% (((derivedTensorSymmetry (ModuleCat.{u + 1} B) Z).hom.app U).naturality
    ((openScalarExtension φ j).hom.app M))]
  simp only [Functor.flip_obj_map]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  have hid := (derivedTensor (ModuleCat.{u + 1} B) Z).map_id
    ((scalarExtension φ Z).obj ((derivedExtension j).obj M))
  erw [hid, NatTrans.id_app, Category.id_comp]
  have hs := etaleNormalizedScalarSymmetry φ Z T H
  rw [tensor_comparison_eq, tensor_comparison_eq] at hs
  simp only [Iso.symm_hom, Iso.app_inv] at hs
  rw [hs, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale
