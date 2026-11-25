/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedLocalizationComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProductSupportMaps
import WeilConjectures.AlgebraicGeometry.Supported.SupportedLocalizationComparisons
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientSecondOpenTensor
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.UnboundedInjectiveModel
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Supported exterior products and localization triangles

Source: Stacks Tags 09XP and 0F1E, and the refinement in the complete proof of
lem-pur-supported-product-localization (blueprint: lem-pur-supported-product-localization).
The third components are the supported exterior products on the actual open product
schemes, transported through the canonical ambient and coefficient comparisons.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry.Etale

private theorem evaluation_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (G G' : D ⥤ E) (H : C ⥤ E)
    (σ : H ≅ F ⋙ G) (ε : R ⋙ F ⟶ 𝟭 D) (τ : G' ≅ G)
    {K K' : D} (a : K ⟶ K') :
    H.map (R.map a) ≫
        (σ.hom.app (R.obj K') ≫ G.map (ε.app K') ≫ τ.inv.app K') =
      (σ.hom.app (R.obj K) ≫ G.map (ε.app K) ≫ τ.inv.app K) ≫ G'.map a := by
  exact (Functor.whiskerLeft R σ.hom ≫ Functor.whiskerRight ε G ≫ τ.inv).naturality a

private theorem coefficientMate_counit
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') (K : C) :
    F'.map (r.app K) ≫ adj'.counit.app (H.obj K) =
      (supportCoefficientMate adj adj' H r).app (R.obj K) ≫ H.map (adj.counit.app K) := by
  simpa [supportCoefficientMate] using mateEquiv_counit_symm adj adj'
    (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r)) K

private theorem evaluation_transport
    {B C C' D D' : Type*}
    [Category B] [Category C] [Category C'] [Category D] [Category D']
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ C'} {R' : C' ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (J : C ⥤ C') (r : R ⟶ J ⋙ R')
    (P : C ⥤ D) (P' : C' ⥤ D') (H : D ⥤ D')
    (G : B ⥤ D) (G' : B ⥤ D')
    (σ : G ≅ F ⋙ P) (σ' : G' ≅ F' ⋙ P')
    (K : C) (e : H.obj (P.obj K) ≅ P'.obj (J.obj K))
    (eF : H.obj (P.obj (F.obj (R.obj K))) ≅ P'.obj (J.obj (F.obj (R.obj K))))
    (he : H.map (P.map (adj.counit.app K)) ≫ e.hom =
      eF.hom ≫ P'.map (J.map (adj.counit.app K))) :
    (σ'.hom.app (R.obj K) ≫
      P'.map ((supportCoefficientMate adj adj' J r).app (R.obj K)) ≫
      eF.inv ≫ H.map (σ.inv.app (R.obj K))) ≫
      H.map (σ.hom.app (R.obj K) ≫ P.map (adj.counit.app K)) ≫ e.hom =
    G'.map (r.app K) ≫
      (σ'.hom.app (R'.obj (J.obj K)) ≫ P'.map (adj'.counit.app (J.obj K))) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, σ.inv_hom_id_app]
  erw [H.map_id, Category.id_comp]
  rw [he, Iso.inv_hom_id_assoc, ← P'.map_comp, ← coefficientMate_counit adj adj' J r K]
  rw [P'.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj, Functor.id_obj] using congrArg
    (fun t ↦ t ≫ P'.map (adj'.counit.app (J.obj K)))
    (σ'.hom.naturality (r.app K)).symm

private theorem restriction_spec (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportOpenRestriction A b U).app M ≫
        (supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app
          ((upperStar (ModuleCat.{u + 1} A) U.ι).obj M) =
      (supportedEtaleSectionsι A T b.openComplement).app M ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M :=
  (exists_unique_supportOpenRestriction A b U).choose_spec.1 M

private noncomputable def support_cut_square (A : Type (u + 1)) [CommRing A]
    {T S C C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h] (c : C ⟶ T) (c' : C' ⟶ S)
    [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :=
  squareUpperStarIso (ModuleCat.{u + 1} A)
    (show CommSq c'.openComplement.ι (supportCutOpenMap h c c' hc) h
      c.openComplement.ι from ⟨(supportCutOpenMap_over h c c' hc).symm⟩)

private noncomputable def support_third_ordinary (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    supportOpenComposite A b c.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) h ⋙ supportOpenComposite A b' c'.openComplement :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) c.openComplement.ι)
      (supportTransport A (supportCutOpenMap h c c' hc)
        (supportOnOpen b c.openComplement) (supportOnOpen b' c'.openComplement)
        (supportRestrictedCut_complement h b c b' c' hb hc)) ≫
    Functor.whiskerRight (support_cut_square A h c c' hc).hom
      (supportedEtaleSections A c'.openComplement
        (supportOnOpen b' c'.openComplement).openComplement)

private theorem composite_unit_eq
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive] :
    Functor.rightDerivedFunctorCompUnit P G ≫
        Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
          P.rightDerivedFunctorIsoMapDerivedCategory.hom G.rightDerivedFunctor) =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G := by
  apply NatTrans.ext
  funext X
  have h := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorCompUnit,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Functor.map_comp, h]

private theorem pullback_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) (G : C' ⥤ D) [F.Additive] [G.Additive]
    (α : F ⟶ P ⋙ G)
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P α = Functor.rightDerivedFunctorNatTrans α ≫ e.hom := by
  apply Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedPullback P α) =
      Functor.rightDerivedPullbackAux P α by simp [Functor.rightDerivedPullback]]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorNatTrans α) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh ≫
        (P ⋙ G).rightDerivedFunctorUnit by
      exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _]
  rw [Category.assoc, he]
  apply NatTrans.ext
  funext X
  simp [Functor.rightDerivedPullbackAux,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit]

private theorem pullback_id_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive]
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P (𝟙 (P ⋙ G)) = e.hom := by
  rw [pullback_eq_comparison P (P ⋙ G) G (𝟙 _) e he]
  simp [Functor.rightDerivedFunctorNatTrans]

private theorem mapDerived_refl
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P] :
    (Functor.mapDerivedCategoryNatIso (Iso.refl P)).hom = 𝟙 P.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategoryFactors.hom.app K)).1
  rw [Functor.mapDerivedCategoryNatIso_fac]
  simp

private theorem mapDerived_nat_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (e' : G ≅ H) :
    (Functor.mapDerivedCategoryNatIso (e ≪≫ e')).hom =
      (Functor.mapDerivedCategoryNatIso e).hom ≫ (Functor.mapDerivedCategoryNatIso e').hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app K)).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac, Functor.mapDerivedCategoryNatIso_fac,
    ← Category.assoc, Functor.mapDerivedCategoryNatIso_fac, Category.assoc,
    ← DerivedCategory.Q.map_comp]
  congr 2

private theorem mapDerived_nat_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryNatIso e.symm).hom =
      (Functor.mapDerivedCategoryNatIso e).inv := by
  apply (cancel_epi (Functor.mapDerivedCategoryNatIso e).hom).1
  rw [← mapDerived_nat_comp, Iso.self_symm_id, mapDerived_refl, Iso.hom_inv_id]

private theorem pullback_square
    {C₀ C₁ C₂ C₃ D : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category D]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian D]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₀]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₂]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₀ ⥤ C₃) (S : C₃ ⥤ C₂)
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [P.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
    (G : C₁ ⥤ D) (G' : C₂ ⥤ D) [G.Additive] [G'.Additive]
    (α : G ⟶ Q ⋙ G') (ε : P ⋙ Q ≅ R ⋙ S) (M : DerivedCategory C₀) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G).inv.app M ≫
        (Functor.rightDerivedPullback R
          (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv ≫
            Functor.whiskerRight ε.hom G' ≫ (Functor.associator R S G').hom)).app M ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorIso S G').hom.app
          (R.mapDerivedCategory.obj M) =
      (Functor.rightDerivedPullback Q α).app (P.mapDerivedCategory.obj M) ≫
        G'.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso P Q).hom.app M ≫
            (Functor.mapDerivedCategoryNatIso ε).hom.app M ≫
            (Functor.mapDerivedCategoryCompIso R S).inv.app M) := by
  have hP := pullback_id_eq_comparison P G
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G)
    (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app P G X)
  have hS := pullback_id_eq_comparison S G'
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso S G')
    (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app S G' X)
  have h₁ := Functor.rightDerivedPullback_comp P Q (P ⋙ Q) (Iso.refl _)
    (𝟙 (P ⋙ G)) α
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv) (by ext; simp) M
  have h₂ := Functor.rightDerivedPullback_comp R S (P ⋙ Q) ε
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv ≫
            Functor.whiskerRight ε.hom G' ≫ (Functor.associator R S G').hom) (𝟙 (S ⋙ G'))
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv) (by ext; simp) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, mapDerived_refl, Category.id_comp,
    hP, hS] at h₁ h₂
  have h₁' := congrArg (fun t ↦ t ≫
    G'.rightDerivedFunctor.map ((Functor.mapDerivedCategoryCompIso P Q).hom.app M)) h₁
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at h₁'
  erw [Category.comp_id] at h₁'
  rw [← h₂, h₁']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

private theorem support_pullback_eq (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
      (supportTransport A h b d hd) = derivedSupportTransport A h b d hd := by
  apply pullback_eq_comparison
  exact (exists_unique_supportTransportComparison A h d).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

private theorem cut_derived_square (A : Type (u + 1)) [CommRing A]
    {T S C C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (c : C ⟶ T) (c' : C' ⟶ S) [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) (K : DerivedCategoryModule A T) :
    (Functor.mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} A) c.openComplement.ι)
        (upperStar (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc))).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso (support_cut_square A h c c' hc)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) h)
        (upperStar (ModuleCat.{u + 1} A) c'.openComplement.ι)).inv.app K =
    ((supportExactPullbackCompIso (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc)
        c.openComplement.ι (c'.openComplement.ι ≫ h)
        (supportCutOpenMap_over h c c' hc).symm).symm ≪≫
      supportExactPullbackCompIso (ModuleCat.{u + 1} A) c'.openComplement.ι h
        (c'.openComplement.ι ≫ h) rfl).hom.app K := by
  simp only [support_cut_square, squareUpperStarIso, supportExactPullbackCompIso,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app]
  rw [mapDerived_nat_comp, mapDerived_nat_inv]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem support_open_comparison_pullback (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) U.ι)
        (𝟙 (supportOpenComposite A b U)) = (supportOpenDerivedComparison A b U).hom := by
  apply pullback_id_eq_comparison
  exact (exists_unique_supportOpenDerivedComparison A b U).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

private theorem third_pullback (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) (K : DerivedCategoryModule A T) :
    (supportOpenDerivedComparison A b c.openComplement).inv.app K ≫
        (Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
          (support_third_ordinary A h b c b' c' hb hc)).app K ≫
        (supportOpenDerivedComparison A b' c'.openComplement).hom.app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) =
      supportTriangleRestrictionThird A h b c b' c' hb hc K := by
  let P := upperStar (ModuleCat.{u + 1} A) c.openComplement.ι
  let Q := upperStar (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc)
  let R := upperStar (ModuleCat.{u + 1} A) h
  let S' := upperStar (ModuleCat.{u + 1} A) c'.openComplement.ι
  let G := supportedEtaleSections A c.openComplement
    (supportOnOpen b c.openComplement).openComplement
  let G' := supportedEtaleSections A c'.openComplement
    (supportOnOpen b' c'.openComplement).openComplement
  let : P.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.openComplement.ι
      inferInstance).preservesKInjectiveComplexes
  let : S'.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c'.openComplement.ι
      inferInstance).preservesKInjectiveComplexes
  have hP : Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G =
      supportOpenDerivedComparison A b c.openComplement := by
    apply Iso.ext
    rw [← support_open_comparison_pullback]
    exact (pullback_id_eq_comparison P G _
      (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app P G X)).symm
  have hS : Functor.mapDerivedCategoryCompRightDerivedFunctorIso S' G' =
      supportOpenDerivedComparison A b' c'.openComplement := by
    apply Iso.ext
    rw [← support_open_comparison_pullback]
    exact (pullback_id_eq_comparison S' G' _
      (by
        ext X
        exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app S' G' X)).symm
  have hs := pullback_square P Q R S' G G'
    (supportTransport A (supportCutOpenMap h c c' hc)
      (supportOnOpen b c.openComplement) (supportOnOpen b' c'.openComplement)
      (supportRestrictedCut_complement h b c b' c' hb hc))
    (support_cut_square A h c c' hc) K
  rw [hP, hS] at hs
  change _ ≫ (Functor.rightDerivedPullback R
    (support_third_ordinary A h b c b' c' hb hc)).app K ≫ _ = _ at hs
  rw [cut_derived_square, support_pullback_eq] at hs
  exact hs

/- The upstream pullback boundary API is bounded below. The normalized support
triangles in this file are unbounded, so use termwise injective K-injective models
to prove the corresponding comparison directly. -/
private theorem boundary_formula
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (S : ShortComplex (C ⥤ D)) [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    (hS : S.ShortExactOnInjectives)
    (δ : S.X₃.rightDerivedFunctor ⟶
      S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (hδ : ∀ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ.app (DerivedCategory.Q.obj I) ≫
          (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I))
    (M : DerivedCategory C) (R : M.InjectiveModel) :
    δ.app M = ShortComplex.rightDerivedδAux hS M R := by
  have hI : δ.app (DerivedCategory.Q.obj R.I) =
      ShortComplex.rightDerivedδQObj hS R.I := by
    apply (cancel_mono ((S.X₁.rightDerivedFunctorObjQIso R.I).hom⟦(1 : ℤ)⟧')).1
    rw [hδ]
    simp [ShortComplex.rightDerivedδQObj, Category.assoc, ← Functor.map_comp]
  have h := δ.naturality R.iso.hom
  dsimp at h
  rw [hI] at h
  apply (cancel_epi (S.X₃.rightDerivedFunctor.map R.iso.hom)).1
  rw [h]
  simp [ShortComplex.rightDerivedδAux, ← Functor.map_comp_assoc]

private theorem boundary_pullback.{uc, uc', ud, vc, vc', vd}
    {C : Type uc} {C' : Type uc'} {D : Type ud}
    [Category.{vc} C] [Category.{vc'} C'] [Category.{vd} D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [IsGrothendieckAbelian.{vc} C] [IsGrothendieckAbelian.{vc'} C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (S : ShortComplex (C ⥤ D)) (S' : ShortComplex (C' ⥤ D))
    [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    [S'.X₁.Additive] [S'.X₂.Additive] [S'.X₃.Additive]
    (hS : S.ShortExactOnInjectives) (hS' : S'.ShortExactOnInjectives)
    (δ : S.X₃.rightDerivedFunctor ⟶
      S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (δ' : S'.X₃.rightDerivedFunctor ⟶
      S'.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (hδ : ∀ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ.app (DerivedCategory.Q.obj I) ≫
          (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I))
    (hδ' : ∀ (I : CochainComplex C' ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ'.app (DerivedCategory.Q.obj I) ≫
          (S'.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S'.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS'.shortExact_mapCochainComplex I))
    (α₁ : S.X₁ ⟶ P ⋙ S'.X₁) (α₂ : S.X₂ ⟶ P ⋙ S'.X₂)
    (α₃ : S.X₃ ⟶ P ⋙ S'.X₃)
    (h₁₂ : S.f ≫ α₂ = α₁ ≫ Functor.whiskerLeft P S'.f)
    (h₂₃ : S.g ≫ α₃ = α₂ ≫ Functor.whiskerLeft P S'.g)
    (M : DerivedCategory C) :
    δ.app M ≫ ((Functor.rightDerivedPullback P α₁).app M)⟦(1 : ℤ)⟧' =
      (Functor.rightDerivedPullback P α₃).app M ≫ δ'.app (P.mapDerivedCategory.obj M) := by
  let R := Classical.choice (DerivedCategory.nonempty_injectiveModel C M)
  let R' := Classical.choice (DerivedCategory.nonempty_injectiveModel C'
    (P.mapDerivedCategory.obj M))
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKInjective.exists_Q_map_eq
    ((P.mapHomologicalComplex _).obj R.I) R'.I
    (P.mapDerivedCategoryFactors.inv.app R.I ≫ P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv)
  have hφ' : P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv =
      P.mapDerivedCategoryFactors.hom.app R.I ≫ DerivedCategory.Q.map φ := by
    rw [hφ, Iso.hom_inv_id_app_assoc]
  have k₁ := Functor.rightDerivedPullback_app_Q_obj P α₁ R.I R'.I φ
  have k₃ := Functor.rightDerivedPullback_app_Q_obj P α₃ R.I R'.I φ
  rw [← hφ'] at k₁ k₃
  have n₁ := (Functor.rightDerivedPullback P α₁).naturality R.iso.hom
  have n₃ := (Functor.rightDerivedPullback P α₃).naturality R.iso.inv
  dsimp at n₁ n₃
  have m₁ : S.X₁.rightDerivedFunctor.map R.iso.hom ≫
      (Functor.rightDerivedPullback P α₁).app M =
      (S.X₁.rightDerivedFunctorObjQIso R.I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α₁ _).app R.I ≫
          (S'.X₁.mapHomologicalComplex _).map φ) ≫
        (S'.X₁.rightDerivedFunctorObjQIso R'.I).inv ≫
          S'.X₁.rightDerivedFunctor.map R'.iso.hom := by
    rw [n₁, ← reassoc_of% k₁, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have m₃ : (Functor.rightDerivedPullback P α₃).app M ≫
      S'.X₃.rightDerivedFunctor.map R'.iso.inv =
      S.X₃.rightDerivedFunctor.map R.iso.inv ≫ (S.X₃.rightDerivedFunctorObjQIso R.I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α₃ _).app R.I ≫
          (S'.X₃.mapHomologicalComplex _).map φ) ≫
        (S'.X₃.rightDerivedFunctorObjQIso R'.I).inv := by
    rw [← k₃, reassoc_of% n₃, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hb := DerivedCategory.triangleOfSESδ_naturality (hS.shortExact_mapCochainComplex R.I)
    (hS'.shortExact_mapCochainComplex R'.I)
    (ShortComplex.mapCochainComplexPullback P α₁ α₂ α₃ h₁₂ h₂₃ R.I R'.I φ)
  simp only [ShortComplex.mapCochainComplexPullback_τ₁,
    ShortComplex.mapCochainComplexPullback_τ₃] at hb
  rw [boundary_formula S hS δ hδ M R, boundary_formula S' hS' δ' hδ' _ R']
  simp only [ShortComplex.rightDerivedδAux, ShortComplex.rightDerivedδQObj, Category.assoc]
  rw [reassoc_of% m₃]
  simp only [← Functor.map_comp, m₁, Iso.inv_hom_id_assoc]
  rw [(shiftFunctor _ (1 : ℤ)).map_comp (DerivedCategory.Q.map _), reassoc_of% hb]

end AlgebraicGeometry.Etale
