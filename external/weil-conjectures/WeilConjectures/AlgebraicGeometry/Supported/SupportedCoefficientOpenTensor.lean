/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientDerivedOpenMate
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenMateQuotient
import WeilConjectures.AlgebraicGeometry.Supported.SupportedTensorComplexSquare
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Open pullback of the supported coefficient tensor comparison

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

/-- Identify the derived first coefficient functor with coefficients followed by the
canonical derived projection inverse image.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] :
    (supportedFirstCoefficients A f g b).mapDerivedCategory ≅
      (supportedCoefficients A b).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))).symm ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A b).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).symm

/-- The analogous comparison for the second projection.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportSecondCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] :
    (supportedSecondCoefficients A f g d).mapDerivedCategory ≅
      (supportedCoefficients A d).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))).symm ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A d).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).symm

end AlgebraicGeometry.Etale

universe w

section CachedSheafProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
set_option backward.isDefEq.respectTransparency.types true

section
variable {C D E C' D' E' : Type*}
  [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']

/-- The normalization equation is kept abstract when specialized to sheaf functors. -/
@[irreducible]
private def tensorNormalization [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (L : C ⥤ C') (J : D ⥤ D') [L.LaxMonoidal] [J.LaxMonoidal]
    (G F₁ F₂ : C ⥤ D) (DG DF₁ DF₂ : C' ⥤ D')
    (eG : L ⋙ DG ⟶ G ⋙ J) (e₁ : L ⋙ DF₁ ⟶ F₁ ⋙ J)
    (e₂ : L ⋙ DF₂ ⟶ F₂ ⋙ J)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N) : Prop :=
  ∀ P Q, t (L.obj P) (L.obj Q) ≫
      (e₁.app P ⊗ₘ e₂.app Q) ≫ Functor.LaxMonoidal.μ J (F₁.obj P) (F₂.obj Q) =
    DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.app (P ⊗ Q) ≫ J.map (τ P Q)

@[irreducible]
private def mapNormalization (L : C ⥤ C') (J : D ⥤ D') (K : E ⥤ E')
    (F : C ⥤ D) (H : D ⥤ E) (F₀ : C ⥤ E)
    (DF : C' ⥤ D') (DH : D' ⥤ E') (DF₀ : C' ⥤ E')
    (eF : L ⋙ DF ⟶ F ⋙ J) (eH : J ⋙ DH ⟶ H ⋙ K)
    (e₀ : L ⋙ DF₀ ⟶ F₀ ⋙ K) (a : F₀ ⟶ F ⋙ H) (da : DF₀ ⟶ DF ⋙ DH) : Prop :=
  ∀ P, da.app (L.obj P) ≫ DH.map (eF.app P) ≫ eH.app (F.obj P) =
    e₀.app P ≫ K.map (a.app P)

@[irreducible]
private def squareCondition [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory E]
    (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (τ₀ : ∀ P Q, G₀.obj (P ⊗ Q) ⟶ F₁₀.obj P ⊗ F₂₀.obj Q)
    (δ : ∀ P Q, H.obj (P ⊗ Q) ⟶ H.obj P ⊗ H.obj Q)
    (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H) : Prop :=
  ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫ δ (F₁.obj P) (F₂.obj Q) =
    τ₀ P Q ≫ (a₁.app P ⊗ₘ a₂.app Q)

end

section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

-- Pass normalized transformations from homotopy models to cochain models.
end

namespace AlgebraicGeometry.Etale
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
private theorem square_inv_eq
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C] {P Q X X' : Scheme.{u}}
    (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X') (a : X' ⟶ X)
    (hp : h ≫ p = q ≫ a)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (supportPullbackSquareIso C h p q a hp K).inv =
      (leftDerivedUpperStarIsoMapDerivedCategory C q).hom.app
        ((upperStar C a).mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso C (CommSq.mk hp))).hom.app K ≫
      (upperStar C h).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory C p).inv.app K) := by
  simp only [supportPullbackSquareIso, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_inv, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapIso_inv]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory C q).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory C a).inv.app K)
  erw [reassoc_of% hn]
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  simp only [squareUpperStarIso, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app, Category.assoc]
end AlgebraicGeometry.Etale

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
  [F.Additive] [H.Additive] [F'.Additive] (a : F' ⟶ F ⋙ H)

private noncomputable def complexCompMap :
    F'.mapHomologicalComplex (.up ℤ) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex a (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv

end

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (H : D ⥤ E) (F₀ : C ⥤ E)
  [F.Additive] [H.Additive] [F₀.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
@[irreducible]
private def mapNatNormalization (a : F₀ ⟶ F ⋙ H)
    (da : F₀.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory) : Prop :=
  mapNormalization DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
    (F₀.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory H.mapDerivedCategory
    F₀.mapDerivedCategory F.mapDerivedCategoryFactors.hom H.mapDerivedCategoryFactors.hom
    F₀.mapDerivedCategoryFactors.hom (complexCompMap F H F₀ a) da
end

section
variable {C D D' E E' : Type*}
  [Category C] [Category D] [Category D'] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian D'] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
  [HasDerivedCategory E] [HasDerivedCategory E']
  (F : C ⥤ D) (F' : C ⥤ D') (a : D ⥤ D') (p : D ⥤ E)
  (q : D' ⥤ E') (h : E ⥤ E')
  [F.Additive] [F'.Additive] [a.Additive] [p.Additive] [q.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits q] [PreservesFiniteColimits q]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end

section
variable {C D E E' : Type*}
  [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory E']
  (F : C ⥤ D) (p : D ⥤ E) (q : D ⥤ E') (h : E ⥤ E')
  [F.Additive] [p.Additive] [q.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits q] [PreservesFiniteColimits q]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end

section
variable {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

/-- Keep the complex and localization tensor structures behind a base-category interface. -/
@[irreducible]
private def tensorNatNormalization
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (curriedTensor _)) : Prop :=
  tensorNormalization DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) (F₁.mapHomologicalComplex (.up ℤ))
    (F₂.mapHomologicalComplex (.up ℤ))
    G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    G.mapDerivedCategoryFactors.hom F₁.mapDerivedCategoryFactors.hom
    F₂.mapDerivedCategoryFactors.hom
    (fun P Q ↦ (τ.app P).app Q) (fun M N ↦ (t.app M).app N)
end

section
variable {C D E : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Category.{w + 1} E] [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (F₁ F₂ : C ⥤ D) (H : D ⥤ E) [F₁.Additive] [F₂.Additive] [H.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compositeTensor_ext [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
    (G : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory E)
    (γ₁ γ₂ : G ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)).obj
        (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory)).obj (curriedTensor _))
    (hγ : ∀ P Q : CochainComplex C ℤ,
      (γ₁.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        ((H.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ⊗ₘ
         (H.mapDerivedCategory.map (F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) =
      (γ₂.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        ((H.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ⊗ₘ
         (H.mapDerivedCategory.map (F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) :
    γ₁ = γ₂ := by
  apply Localization.natTrans₂_ext DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ))
  intro P Q
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some.reduced
  let R := Λ.resolutionFunctor.obj Q
  let s := DerivedCategory.Q.map (Λ.resolutionNatTrans.app Q)
  have hs : (HomologicalComplex.quasiIso C (.up ℤ)) (Λ.resolutionNatTrans.app Q) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    exact Λ.quasiIso_resolutionNatTrans_app Q
  have : IsIso s := (Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))) _ hs
  have hR : (γ₁.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R) =
      (γ₂.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R) := by
    have hflat := (F₂ ⋙ H).kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj
      Λ ObjectProperty.flat.essImage_ι_le Q
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R))) :=
      AlgebraicGeometry.Etale.tensorLocalization_isIso _ _ hflat
    have h := hγ P R
    exact (cancel_mono _).1 h
  apply (cancel_epi ((G.obj (DerivedCategory.Q.obj P)).map s)).1
  erw [(γ₁.app (DerivedCategory.Q.obj P)).naturality s,
    (γ₂.app (DerivedCategory.Q.obj P)).naturality s]
  exact congrArg (fun k ↦ k ≫ _) hR

end

private theorem model_square
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
    (L : C ⥤ C') (J : D ⥤ D') (K : E ⥤ E')
    [L.LaxMonoidal] [J.LaxMonoidal] [K.LaxMonoidal]
    (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
    (DG DF₁ DF₂ : C' ⥤ D') (DG₀ DF₁₀ DF₂₀ : C' ⥤ E') (DH : D' ⥤ E')
    (eG : L ⋙ DG ⟶ G ⋙ J) (eF₁ : L ⋙ DF₁ ⟶ F₁ ⋙ J)
    (eF₂ : L ⋙ DF₂ ⟶ F₂ ⋙ J) (eG₀ : L ⋙ DG₀ ⟶ G₀ ⋙ K)
    (eF₁₀ : L ⋙ DF₁₀ ⟶ F₁₀ ⋙ K) (eF₂₀ : L ⋙ DF₂₀ ⟶ F₂₀ ⋙ K)
    (eH : J ⋙ DH ⟶ H ⋙ K)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (τ₀ : ∀ P Q, G₀.obj (P ⊗ Q) ⟶ F₁₀.obj P ⊗ F₂₀.obj Q)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (t₀ : ∀ M N, DG₀.obj (M ⊗ N) ⟶ DF₁₀.obj M ⊗ DF₂₀.obj N)
    (δ : (Functor.postcompose₂.obj DH).obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ E').obj DH).obj DH).obj (curriedTensor E'))
    (δc : ∀ P Q, H.obj (P ⊗ Q) ⟶ H.obj P ⊗ H.obj Q)
    (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
    (da₀ : DG₀ ⟶ DG ⋙ DH) (da₁ : DF₁₀ ⟶ DF₁ ⋙ DH)
    (da₂ : DF₂₀ ⟶ DF₂ ⋙ DH)
    (ht : ∀ P Q, t (L.obj P) (L.obj Q) ≫
        (eF₁.app P ⊗ₘ eF₂.app Q) ≫ Functor.LaxMonoidal.μ J (F₁.obj P) (F₂.obj Q) =
      DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.app (P ⊗ Q) ≫ J.map (τ P Q))
    (ht₀ : ∀ P Q, t₀ (L.obj P) (L.obj Q) ≫
        (eF₁₀.app P ⊗ₘ eF₂₀.app Q) ≫ Functor.LaxMonoidal.μ K (F₁₀.obj P) (F₂₀.obj Q) =
      DG₀.map (Functor.LaxMonoidal.μ L P Q) ≫ eG₀.app (P ⊗ Q) ≫ K.map (τ₀ P Q))
    (hδ : ∀ P Q, (δ.app (J.obj P)).app (J.obj Q) ≫
        (eH.app P ⊗ₘ eH.app Q) ≫ Functor.LaxMonoidal.μ K (H.obj P) (H.obj Q) =
      DH.map (Functor.LaxMonoidal.μ J P Q) ≫ eH.app (P ⊗ Q) ≫ K.map (δc P Q))
    (ha₀ : ∀ P, da₀.app (L.obj P) ≫ DH.map (eG.app P) ≫ eH.app (G.obj P) =
      eG₀.app P ≫ K.map (a₀.app P))
    (ha₁ : ∀ P, da₁.app (L.obj P) ≫ DH.map (eF₁.app P) ≫ eH.app (F₁.obj P) =
      eF₁₀.app P ≫ K.map (a₁.app P))
    (ha₂ : ∀ P, da₂.app (L.obj P) ≫ DH.map (eF₂.app P) ≫ eH.app (F₂.obj P) =
      eF₂₀.app P ≫ K.map (a₂.app P))
    (hs : ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫ δc (F₁.obj P) (F₂.obj Q) =
      τ₀ P Q ≫ (a₁.app P ⊗ₘ a₂.app Q)) (P Q : C) :
    (da₀.app (L.obj P ⊗ L.obj Q) ≫ DH.map (t (L.obj P) (L.obj Q)) ≫
        (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q))) ≫
      ((DH.map (eF₁.app P) ≫ eH.app (F₁.obj P)) ⊗ₘ
        (DH.map (eF₂.app Q) ≫ eH.app (F₂.obj Q))) ≫
      Functor.LaxMonoidal.μ K (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)) =
    (t₀ (L.obj P) (L.obj Q) ≫ (da₁.app (L.obj P) ⊗ₘ da₂.app (L.obj Q))) ≫
      ((DH.map (eF₁.app P) ≫ eH.app (F₁.obj P)) ⊗ₘ
        (DH.map (eF₂.app Q) ≫ eH.app (F₂.obj Q))) ≫
      Functor.LaxMonoidal.μ K (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)) := by
  have hδn := congr_app (δ.naturality (eF₁.app P)) (DF₂.obj (L.obj Q))
  have hδn' := (δ.app (J.obj (F₁.obj P))).naturality (eF₂.app Q)
  change DH.map (eF₁.app P ▷ DF₂.obj (L.obj Q)) ≫
      (δ.app (J.obj (F₁.obj P))).app (DF₂.obj (L.obj Q)) =
    (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.map (eF₁.app P) ▷ DH.obj (DF₂.obj (L.obj Q))) at hδn
  change DH.map (J.obj (F₁.obj P) ◁ eF₂.app Q) ≫
      (δ.app (J.obj (F₁.obj P))).app (J.obj (F₂.obj Q)) =
    (δ.app (J.obj (F₁.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.obj (J.obj (F₁.obj P)) ◁ DH.map (eF₂.app Q)) at hδn'
  have hn : DH.map (eF₁.app P ⊗ₘ eF₂.app Q) ≫
        (δ.app (J.obj (F₁.obj P))).app (J.obj (F₂.obj Q)) =
      (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
        (DH.map (eF₁.app P) ⊗ₘ DH.map (eF₂.app Q)) := by
    rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hδn',
      ← Category.assoc, hδn, Category.assoc, ← MonoidalCategory.tensorHom_def]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← reassoc_of% hn, hδ]
  have htn := congrArg DH.map (ht P Q)
  simp only [CategoryTheory.Functor.map_comp] at htn
  erw [reassoc_of% htn]
  erw [reassoc_of% (eH.naturality (τ P Q))]
  erw [← reassoc_of% (da₀.naturality (Functor.LaxMonoidal.μ L P Q))]
  rw [reassoc_of% ha₀]
  have hsk := congrArg K.map (hs P Q)
  simp only [CategoryTheory.Functor.map_comp] at hsk
  erw [hsk]
  rw [← reassoc_of% ht₀, ← Functor.LaxMonoidal.μ_natural]
  erw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [ha₁, ha₂]
  rfl

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

private def squareLeft
    (G F₁ F₂ : C ⥤ D) (G₀ : C ⥤ E) (H : D ⥤ E)
    (a₀ : G₀ ⟶ G ⋙ H)
    (t : (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁ ⋙ H)).obj (F₂ ⋙ H)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.map a₀).app (curriedTensor _) ≫
    (Functor.postcompose₂.obj H).map t ≫
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).map δ

private def squareRight
    (G₀ F₁₀ F₂₀ F₁ F₂ : C ⥤ E)
    (a₁ : F₁₀ ⟶ F₁) (a₂ : F₂₀ ⟶ F₂)
    (t₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _) :=
  t₀ ≫ (((Functor.whiskeringLeft₂ _).map a₁).app F₂₀).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj F₁).map a₂).app (curriedTensor _)

private theorem squareLeft_app
    (G F₁ F₂ : C ⥤ D) (G₀ : C ⥤ E) (H : D ⥤ E)
    (a₀ : G₀ ⟶ G ⋙ H)
    (t : (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) (M N : C) :
    ((squareLeft G F₁ F₂ G₀ H a₀ t δ).app M).app N =
      a₀.app (M ⊗ N) ≫ H.map ((t.app M).app N) ≫ (δ.app (F₁.obj M)).app (F₂.obj N) := by
  simp only [squareLeft, NatTrans.comp_app]
  rfl

private theorem squareRight_app
    (G₀ F₁₀ F₂₀ F₁ F₂ : C ⥤ E)
    (a₁ : F₁₀ ⟶ F₁) (a₂ : F₂₀ ⟶ F₂)
    (t₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _)) (M N : C) :
    ((squareRight G₀ F₁₀ F₂₀ F₁ F₂ a₁ a₂ t₀).app M).app N =
      (t₀.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N) := by
  simp only [squareRight, NatTrans.comp_app, MonoidalCategory.tensorHom_def]
  rfl
end

section
variable {C : Type v₁} {D : Type v₂} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
    (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
      (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
  (t : AlgebraicGeometry.Etale.supportedDerivedComparisonHom G F₁ F₂)
  (ht : AlgebraicGeometry.Etale.supportedDerivedComparisonCondition G F₁ F₂ τ t)
end

section
variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']

private def conjugateTensor (H H' : C' ⥤ D') (e : H ≅ H')
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj H').obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H').obj H').obj (curriedTensor _) :=
  (Functor.postcompose₂.map e.inv).app (curriedTensor _) ≫ δ ≫
    (((Functor.whiskeringLeft₂ _).map e.hom).app H).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj H').map e.hom).app (curriedTensor _)

end

section
variable {C : Type v₁} {D : Type v₂} [Category.{w} C] [Category.{w} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesColimitsOfSize.{0, 0} F]
end

section
variable {C : Type v₁} {D : Type v₂} {E : Type v₃}
  [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive] [H.Additive] [H.Monoidal]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [PreservesColimitsOfSize.{0, 0} H]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor D))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor E))
  (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complexSquare_cached
    (hs : ∀ P Q, AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition
      G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ P Q) :
    squareCondition (G.mapHomologicalComplex (.up ℤ))
      (F₁.mapHomologicalComplex (.up ℤ)) (F₂.mapHomologicalComplex (.up ℤ))
      (G₀.mapHomologicalComplex (.up ℤ)) (F₁₀.mapHomologicalComplex (.up ℤ))
      (F₂₀.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
      (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
        G F₁ F₂ τ).app P).app Q)
      (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
        G₀ F₁₀ F₂₀ τ₀).app P).app Q)
      (fun P Q ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
        (.up ℤ) H).app P).app Q)
      (complexCompMap G H G₀ a₀) (complexCompMap F₁ H F₁₀ a₁)
      (complexCompMap F₂ H F₂₀ a₂) := by
  unfold squareCondition
  intro P Q
  have h := hs P Q
  unfold AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition at h
  exact h
end

section
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{u + 1} C] {X : AlgebraicGeometry.Scheme.{u}}
  (G F₁ F₂ : C ⥤ Sheaf X.smallEtaleTopology C)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C X))

end

section
variable {C D E : Type*}
  [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive] [H.Additive] [H.Monoidal]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
  [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [PreservesColimitsOfSize.{0, 0} H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor D))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor E))
  (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
  (da₀ : G₀.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (da₁ : F₁₀.mapDerivedCategory ⟶ F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (da₂ : F₂₀.mapDerivedCategory ⟶ F₂.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (curriedTensor _))
  (t₀ : (Functor.postcompose₂.obj G₀.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀.mapDerivedCategory).obj
      F₂₀.mapDerivedCategory).obj (curriedTensor _))
  (δ : (Functor.postcompose₂.obj H.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj H.mapDerivedCategory).obj
      H.mapDerivedCategory).obj (curriedTensor _))
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem derived_square
    (ht : tensorNatNormalization G F₁ F₂
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (ht₀ : tensorNatNormalization G₀ F₁₀ F₂₀
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G₀ F₁₀ F₂₀ τ₀) t₀)
    (hδ : tensorNatNormalization H H H
      (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H) δ)
    (ha₀ : mapNatNormalization G H G₀ a₀ da₀)
    (ha₁ : mapNatNormalization F₁ H F₁₀ a₁ da₁)
    (ha₂ : mapNatNormalization F₂ H F₂₀ a₂ da₂)
    (hs : ∀ P Q, AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition
      G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ P Q)
    : squareLeft G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
        G₀.mapDerivedCategory H.mapDerivedCategory da₀ t δ =
      squareRight G₀.mapDerivedCategory F₁₀.mapDerivedCategory F₂₀.mapDerivedCategory
        (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
        (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory) da₁ da₂ t₀ := by
  unfold tensorNatNormalization tensorNormalization at ht ht₀ hδ
  unfold mapNatNormalization mapNormalization at ha₀ ha₁ ha₂
  have hc := complexSquare_cached G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ hs
  unfold squareCondition at hc
  apply compositeTensor_ext F₁ F₂ H
  intro P Q
  rw [squareLeft_app, squareRight_app]
  exact model_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ))
    (F₁.mapHomologicalComplex (.up ℤ)) (F₂.mapHomologicalComplex (.up ℤ))
    (G₀.mapHomologicalComplex (.up ℤ))
    (F₁₀.mapHomologicalComplex (.up ℤ)) (F₂₀.mapHomologicalComplex (.up ℤ))
    (H.mapHomologicalComplex (.up ℤ))
    G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    G₀.mapDerivedCategory F₁₀.mapDerivedCategory F₂₀.mapDerivedCategory H.mapDerivedCategory
    G.mapDerivedCategoryFactors.hom F₁.mapDerivedCategoryFactors.hom
    F₂.mapDerivedCategoryFactors.hom G₀.mapDerivedCategoryFactors.hom
    F₁₀.mapDerivedCategoryFactors.hom F₂₀.mapDerivedCategoryFactors.hom
    H.mapDerivedCategoryFactors.hom
    (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
      G F₁ F₂ τ).app P).app Q)
    (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
      G₀ F₁₀ F₂₀ τ₀).app P).app Q)
    (fun M N ↦ (t.app M).app N) (fun M N ↦ (t₀.app M).app N) δ
    (fun P Q ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H).app P).app Q)
    (complexCompMap G H G₀ a₀) (complexCompMap F₁ H F₁₀ a₁)
    (complexCompMap F₂ H F₂₀ a₂) da₀ da₁ da₂
    ht ht₀ hδ ha₀ ha₁ ha₂ hc P Q
end

namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
end AlgebraicGeometry.Etale

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C]
end AlgebraicGeometry.Etale

end
section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{u + 1} C]
  [AlgebraicGeometry.Etale.UpperStarPreservesFlat C]
  {X Y : AlgebraicGeometry.Scheme.{u}} (h : Y ⟶ X)
variable
  (G F₁ F₂ : C ⥤ (Sheaf X.smallEtaleTopology C)) (G₀ F₁₀ F₂₀ : C ⥤ (Sheaf Y.smallEtaleTopology C))
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
  [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [(F₂ ⋙ (AlgebraicGeometry.Etale.upperStar C h)).PreservesFlat] [(F₂ ⋙
    (AlgebraicGeometry.Etale.upperStar C h)).IsLeftAdjoint]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj
      (AlgebraicGeometry.Etale.supportedSheafTensorGeneric C X))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj
      (AlgebraicGeometry.Etale.supportedSheafTensorGeneric C Y))
  (a₀ : G₀ ⟶ G ⋙ (AlgebraicGeometry.Etale.upperStar C h)) (a₁ : F₁₀ ⟶ F₁ ⋙
    (AlgebraicGeometry.Etale.upperStar C h)) (a₂ : F₂₀ ⟶ F₂ ⋙ (AlgebraicGeometry.Etale.upperStar C
    h))
  (da₀ : G₀.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (da₁ : F₁₀.mapDerivedCategory ⟶ F₁.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (da₂ : F₂₀.mapDerivedCategory ⟶ F₂.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C X))
  (t₀ : (Functor.postcompose₂.obj G₀.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀.mapDerivedCategory).obj
      F₂₀.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C Y))
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
end

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
end AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
end AlgebraicGeometry.Etale

end CachedSheafProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end AlgebraicGeometry.Etale
