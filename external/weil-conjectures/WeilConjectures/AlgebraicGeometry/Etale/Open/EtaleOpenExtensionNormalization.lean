/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCochainConjugate
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenDerivedConjugate
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenLocalizationMate
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarRepresentativeMate

/-! # The canonical open/scalar adjoint comparison has the prescribed cochain normalization. -/

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

section Mates
open CategoryTheory.Functor

private theorem normalization_cube
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₀ M₀ : C ⥤ D} {R₀ S₀ : D ⥤ C} {L M : E ⥤ F} {R S : F ⥤ E}
    (a₀ : L₀ ⊣ R₀) (b₀ : M₀ ⊣ S₀) (a : L ⊣ R) (b : M ⊣ S)
    {Q : C ⥤ E} {P : D ⥤ F}
    (c : L₀ ⟶ M₀) (d : L ⟶ M)
    (α : TwoSquare Q L₀ L P) (β : TwoSquare Q M₀ M P)
    (e₀ : S₀ ⟶ R₀) (e : S ⟶ R)
    (hc : conjugateEquiv b₀ a₀ c = e₀) (hd : conjugateEquiv b a d = e)
    (hr : (mateEquiv b₀ b β).whiskerBottom e =
      (mateEquiv a₀ a α).whiskerTop e₀) :
    ∀ X, d.app (Q.obj X) ≫ β.app X = α.app X ≫ P.map (c.app X) := by
  have h : β.whiskerRight d = α.whiskerLeft c := by
    apply (mateEquiv b₀ a).injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp, hc, hd]
    exact hr
  exact fun X ↦ congrArg (fun t ↦ t.app X) h

private theorem normalization_components
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {F₁₀ : C₀ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {F₂₀ : C₁ ⥤ C₃} {G₂₀ : C₃ ⥤ C₁}
    {H₁₀ : C₀ ⥤ C₂} {I₁₀ : C₂ ⥤ C₀} {H₂₀ : C₂ ⥤ C₃} {I₂₀ : C₃ ⥤ C₂}
    {F₁ : D₀ ⥤ D₁} {G₁ : D₁ ⥤ D₀} {F₂ : D₁ ⥤ D₃} {G₂ : D₃ ⥤ D₁}
    {H₁ : D₀ ⥤ D₂} {I₁ : D₂ ⥤ D₀} {H₂ : D₂ ⥤ D₃} {I₂ : D₃ ⥤ D₂}
    (a₁₀ : F₁₀ ⊣ G₁₀) (a₂₀ : F₂₀ ⊣ G₂₀)
    (b₁₀ : H₁₀ ⊣ I₁₀) (b₂₀ : H₂₀ ⊣ I₂₀)
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (b₁ : H₁ ⊣ I₁) (b₂ : H₂ ⊣ I₂)
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃}
    (α₁ : TwoSquare Q₀ F₁₀ F₁ Q₁) (β₂ : TwoSquare Q₂ H₂₀ H₂ Q₃)
    (γ₁ : TwoSquare G₁₀ Q₁ Q₀ G₁) (γ₂ : TwoSquare G₂₀ Q₃ Q₁ G₂)
    (δ₁ : TwoSquare I₁₀ Q₂ Q₀ I₁) (δ₂ : TwoSquare I₂₀ Q₃ Q₂ I₂)
    (c : F₁₀ ⋙ F₂₀ ⟶ H₁₀ ⋙ H₂₀) (d : F₁ ⋙ F₂ ⟶ H₁ ⋙ H₂)
    (e₀ : I₂₀ ⋙ I₁₀ ⟶ G₂₀ ⋙ G₁₀) (e : I₂ ⋙ I₁ ⟶ G₂ ⋙ G₁)
    (hc : conjugateEquiv (b₁₀.comp b₂₀) (a₁₀.comp a₂₀) c = e₀)
    (hd : conjugateEquiv (b₁.comp b₂) (a₁.comp a₂) d = e)
    (mα₁ : mateEquiv a₁₀ a₁ α₁ = γ₁) (mβ₂ : mateEquiv b₂₀ b₂ β₂ = δ₂)
    (hr : ∀ Z, δ₁.app (I₂₀.obj Z) ≫ I₁.map (δ₂.app Z) ≫ e.app (Q₃.obj Z) =
      Q₀.map (e₀.app Z) ≫ γ₁.app (G₂₀.obj Z) ≫ G₁.map (γ₂.app Z))
    (P : C₀)
    (r₁ : H₁.obj (Q₀.obj P) ⟶ Q₂.obj (H₁₀.obj P))
    (r₂ : F₂.obj (Q₁.obj (F₁₀.obj P)) ⟶ Q₃.obj (F₂₀.obj (F₁₀.obj P)))
    (h₁ : ((mateEquiv b₁₀ b₁).symm δ₁).app P = r₁)
    (h₂ : ((mateEquiv a₂₀ a₂).symm γ₂).app (F₁₀.obj P) = r₂) :
    d.app (Q₀.obj P) ≫ H₂.map r₁ ≫ β₂.app (H₁₀.obj P) =
      F₂.map (α₁.app P) ≫ r₂ ≫ Q₃.map (c.app P) := by
  let α₂ := (mateEquiv a₂₀ a₂).symm γ₂
  let β₁ := (mateEquiv b₁₀ b₁).symm δ₁
  have hα : mateEquiv (a₁₀.comp a₂₀) (a₁.comp a₂) (α₁ ≫ᵥ α₂) = γ₂ ≫ₕ γ₁ := by
    rw [mateEquiv_hcomp, mα₁]
    simp only [α₂, Equiv.apply_symm_apply]
  have hβ : mateEquiv (b₁₀.comp b₂₀) (b₁.comp b₂) (β₁ ≫ᵥ β₂) = δ₂ ≫ₕ δ₁ := by
    rw [mateEquiv_hcomp, mβ₂]
    simp only [β₁, Equiv.apply_symm_apply]
  have hr' : (mateEquiv (b₁₀.comp b₂₀) (b₁.comp b₂) (β₁ ≫ᵥ β₂)).whiskerBottom e =
      (mateEquiv (a₁₀.comp a₂₀) (a₁.comp a₂) (α₁ ≫ᵥ α₂)).whiskerTop e₀ := by
    rw [hα, hβ]
    ext Z
    simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      TwoSquare.mk, Category.assoc] using hr Z
  have h := normalization_cube (a₁₀.comp a₂₀) (b₁₀.comp b₂₀) (a₁.comp a₂) (b₁.comp b₂)
    c d (α₁ ≫ᵥ α₂) (β₁ ≫ᵥ β₂) e₀ e hc hd hr' P
  rw [← h₁, ← h₂]
  simpa only [TwoSquare.vComp_app, α₂, β₁, Category.assoc] using h

end Mates

section ExactFactors
open CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem square_inverse_factors
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (M : D ⥤ F) (N : C ⥤ E) (O : E ⥤ F)
    [L.Additive] [M.Additive] [N.Additive] [O.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (e : L ⋙ M ≅ N ⋙ O) (P : CochainComplex C ℤ) :
    M.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        M.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app P) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) ≫
        O.mapDerivedCategoryFactors.inv.app ((N.mapHomologicalComplex (.up ℤ)).obj P) ≫
        O.mapDerivedCategory.map (N.mapDerivedCategoryFactors.inv.app P) := by
  have hL := Functor.mapDerivedCategoryCompIso_hom_app_factors L M P
  have hN := Functor.mapDerivedCategoryCompIso_hom_app_factors N O P
  apply (cancel_mono
    (O.mapDerivedCategory.map (N.mapDerivedCategoryFactors.hom.app P) ≫
      O.mapDerivedCategoryFactors.hom.app ((N.mapHomologicalComplex (.up ℤ)).obj P))).mp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [hN, Functor.mapDerivedCategoryNatIso_fac]
  rw [← reassoc_of% hL, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem open_inverse_factors
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    (Sheaf.restrictScalars U.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((upperStar (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).map
        ((upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.inv.app P) ≫
      (openDerivedRestrictScalarsIso φ j).hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (openRestrictScalarsIso φ j) (.up ℤ)).hom.app P) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.inv.app
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (derivedRestriction (A := A) j).map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app P) := by
  exact square_inverse_factors _ _ _ _ (openRestrictScalarsIso φ j) P

end ExactFactors

section Comparisons
open CategoryTheory.Limits
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh upperStar lowerStar openImmersionLowerShriek
  scalarExtensionRepresentative openScalarExtensionZero openScalarExtension
  openDerivedRestrictScalarsIso openRestrictScalarsIso
  derivedOpenImmersionLowerShriekUpperStarAdjunction Adjunction.ofIsRightAdjoint
  ProEtale.etaleSheafExtendScalarsAdjunction openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapHomologicalComplex

/-- The canonical open/scalar adjoint comparison has the prescribed cochain normalization.
Source: Stacks Tags 0E8I, 03DI and 06YY; parent proof step 1.

Proof: Transpose the two paths using the composite of the open adjunction and
scalar adjunction. The scalar representative transposes to the localized
ordinary scalar unit. The exact open adjunction unit is the localization of
its ordinary unit under the exact localization factor isomorphisms. Naturality
of those factors and the composition law for the derived right-adjoint square
identify the transposed paths. At the ordinary level the equality is precisely
the unit identity for uniqueness of left adjoints defining q-zero. The
homological-complex comparison applies that identity degree by degree. Cancel
the composite adjunction hom equivalence. This gives the equation for every
complex, hence in particular for the K-flat complexes in the normalization
predicate. The argument is valid for the empty open immersion and zero rings.
(blueprint: lem-coef-etale-open-extension-normalization). -/
theorem etaleOpenExtensionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    OpenScalarExtensionNormalization φ j (openScalarExtension φ j) := by
  dsimp only [OpenScalarExtensionNormalization]
  intro P _
  exact normalization_components
    (F₁₀ := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
    (G₁₀ := (upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
    (F₂₀ := (ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ))
    (G₂₀ := (Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ))
    (H₁₀ := (ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ))
    (I₁₀ := (Sheaf.restrictScalars U.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ))
    (H₂₀ := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ))
    (I₂₀ := (upperStar (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ))
    (F₁ := derivedExtension (A := A) j) (G₁ := derivedRestriction (A := A) j)
    (F₂ := scalarExtension φ X) (G₂ := Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
    (H₁ := scalarExtension φ U) (I₁ := Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
    (H₂ := derivedExtension (A := B) j) (I₂ := derivedRestriction (A := B) j)
    (Q₀ := DerivedCategory.Q) (Q₁ := DerivedCategory.Q)
    (Q₂ := DerivedCategory.Q) (Q₃ := DerivedCategory.Q)
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).mapHomologicalComplex (.up ℤ))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).mapHomologicalComplex (.up ℤ))
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (TwoSquare.mk _ _ _ _
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom)
    (TwoSquare.mk _ _ _ _
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom)
    (TwoSquare.mk _ _ _ _ (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.inv)
    (TwoSquare.mk _ _ _ _
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.inv)
    (TwoSquare.mk _ _ _ _
      (Sheaf.restrictScalars U.smallEtaleTopology φ).mapDerivedCategoryFactors.inv)
    (TwoSquare.mk _ _ _ _ (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.inv)
    (Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ j) (.up ℤ)).hom
    (openScalarExtension φ j).hom
    (Functor.mapHomologicalComplexCompIso (openRestrictScalarsIso φ j) (.up ℤ)).hom
    (openDerivedRestrictScalarsIso φ j).hom
    (etaleOpenScalarCochainConjugate φ j) (etaleOpenScalarDerivedConjugate φ j)
    (etaleOpenLocalizationMate A j) (etaleOpenLocalizationMate B j)
    (open_inverse_factors φ j) P
    (scalarExtensionRepresentative φ U P)
    (scalarExtensionRepresentative φ X
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P))
    (etaleScalarRepresentativeMate φ U P) (etaleScalarRepresentativeMate φ X _)

end Comparisons

end AlgebraicGeometry.Etale
