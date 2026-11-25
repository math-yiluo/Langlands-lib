/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenBetaSiteTransport
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenTailSiteTransport

/-!
# Site comparison for the clopen alpha

Source: Stacks Project, Tags 099R, 09AF and 0F7B; steps 2--4 of
lem-cbc-finite-clopen-mate-site-transport
(blueprint: lem-cbc-finite-clopen-alpha-site-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Etale.ClopenMateNormalization

namespace ExactAlphaLocalization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (G : A ⥤ B) (Q : B ⥤ D) (P : A ⥤ C) (H : C ⥤ D)
  [G.Additive] [Q.Additive] [P.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem square_fac (e : G ⋙ Q ⟶ P ⋙ H) (K : HomotopyCategory.Plus A) :
    (clopenLocalizedSquarePlus e).app
        (DerivedCategory.Plus.Qh.obj K) ≫
      H.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K) =
    Q.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      Q.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) := by
  exact clopenLocalizedSquarePlus_factorization e K

private theorem iso_square_fac (e : G ⋙ Q ≅ P ⋙ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapDerivedCategoryPlusCompIso G Q).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusCompIso P H).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
      H.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K) =
    Q.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      Q.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh P H K]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh e K]
  rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G Q K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem iso_square_eq (e : G ⋙ Q ≅ P ⋙ H) :
    clopenLocalizedSquarePlus e.hom =
      ((Functor.mapDerivedCategoryPlusCompIso G Q).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusCompIso P H).hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A)
  intro K
  apply (cancel_mono (H.mapDerivedCategoryPlus.map
    (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K))).1
  simpa only [Category.assoc] using
    (square_fac G Q P H e.hom K).trans (iso_square_fac G Q P H e K).symm

variable [EnoughInjectives A] [EnoughInjectives C]

private theorem baseChange_fac (e : G ⋙ Q ⟶ P ⋙ H) (K : HomotopyCategory.Plus A) :
    (Functor.whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv
        Q.mapDerivedCategoryPlus ≫
      Functor.rightDerivedFunctorPlusBaseChange e ≫
      Functor.whiskerLeft P.mapDerivedCategoryPlus
        H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom).app
          (DerivedCategory.Plus.Qh.obj K) ≫
      H.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K) =
    Q.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      Q.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) := by
  have hg := congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  have hh := congr_app H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    (P.mapHomotopyCategoryPlus.obj K)
  have he := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hg hh he
  have hgi : G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (DerivedCategory.Plus.Qh.obj K) =
      G.mapDerivedCategoryPlusFactorsh.hom.app K ≫ G.rightDerivedFunctorPlusUnith.app K := by
    rw [← cancel_mono (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app _)]
    simp only [Category.assoc, hg, Iso.inv_hom_id_app, Iso.hom_inv_id_app]
    rfl
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [hgi, Q.mapDerivedCategoryPlus.map_comp]
  rw [← reassoc_of%
    H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
      (P.mapDerivedCategoryPlusFactorsh.hom.app K)]
  simp only [Category.assoc]
  rw [reassoc_of% he]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
  rw [← H.rightDerivedFunctorPlus.map_comp_assoc, Iso.inv_hom_id_app,
    H.rightDerivedFunctorPlus.map_id, Category.id_comp]
  rw [reassoc_of% hh]
  simp only [Iso.inv_hom_id_app]
  simp only [DerivedCategory.Plus.Qh.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id]

private theorem baseChange_eq (e : G ⋙ Q ⟶ P ⋙ H) :
    Functor.whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv
        Q.mapDerivedCategoryPlus ≫
      Functor.rightDerivedFunctorPlusBaseChange e ≫
      Functor.whiskerLeft P.mapDerivedCategoryPlus
        H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom =
      clopenLocalizedSquarePlus e := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A)
  intro K
  apply (cancel_mono (H.mapDerivedCategoryPlus.map
    (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K))).1
  simpa only [Category.assoc] using
    (baseChange_fac G Q P H e K).trans (square_fac G Q P H e K).symm

private theorem baseChange_eq_app (e : G ⋙ Q ⟶ P ⋙ H)
    (K : DerivedCategory.Plus A) :
    (Functor.rightDerivedFunctorPlusBaseChange e).app K =
      Q.mapDerivedCategoryPlus.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K) ≫
      (clopenLocalizedSquarePlus e).app K ≫
      H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (P.mapDerivedCategoryPlus.obj K) := by
  rw [← cancel_epi (Q.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K))]
  rw [← cancel_mono (H.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
    (P.mapDerivedCategoryPlus.obj K))]
  have he := congr_app (baseChange_eq G Q P H e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he
  dsimp only [Functor.comp_obj] at he ⊢
  simpa only [Category.assoc, ← Q.mapDerivedCategoryPlus.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
    Q.mapDerivedCategoryPlus.map_id, Category.id_comp, Category.comp_id] using he

section Cube

variable {B' C' A₀ B₀ B₀' C₀' : Type*}
  [Category* B'] [Category* C'] [Category* A₀] [Category* B₀]
  [Category* B₀'] [Category* C₀']
  [Abelian B'] [Abelian C'] [Abelian A₀] [Abelian B₀]
  [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory A₀] [HasDerivedCategory B₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [EnoughInjectives B'] [EnoughInjectives A₀] [EnoughInjectives B₀']
  (G₁ : A ⥤ B) (H₁ : B' ⥤ C') (G₀ : A₀ ⥤ B₀) (H₀ : B₀' ⥤ C₀')
  (P₁ : A ⥤ B') (Q₁ : B ⥤ C') (P₀ : A₀ ⥤ B₀') (Q₀ : B₀ ⥤ C₀')
  (U : A ⥤ A₀) (V : B ⥤ B₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G₁.Additive] [H₁.Additive] [G₀.Additive] [H₀.Additive]
  [P₁.Additive] [Q₁.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits H₀] [PreservesFiniteColimits H₀]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

private theorem cube
    (e : G₁ ⋙ Q₁ ⟶ P₁ ⋙ H₁) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G₁ ⋙ V ≅ U ⋙ G₀) (b : H₁ ⋙ V' ≅ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q₁ ⋙ V') (d : U ⋙ P₀ ≅ P₁ ⋙ U')
    (h : ∀ F : A, V'.map (e.app F) ≫ b.hom.app (P₁.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G₁.obj F) ≫ Q₀.map (a.hom.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory.Plus A) :
    V'.mapDerivedCategoryPlus.map
        ((clopenLocalizedSquarePlus e).app K) ≫
      ((Functor.mapDerivedCategoryPlusCompIso H₁ V').symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso b ≪≫
        Functor.mapDerivedCategoryPlusCompIso U' H₀).hom.app
          (P₁.mapDerivedCategoryPlus.obj K) ≫
      H₀.mapDerivedCategoryPlus.map
        (((Functor.mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso d ≪≫
          Functor.mapDerivedCategoryPlusCompIso P₁ U').inv.app K) =
    ((Functor.mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso c ≪≫
        Functor.mapDerivedCategoryPlusCompIso Q₁ V').inv.app
          (G₁.mapDerivedCategoryPlus.obj K) ≫
      Q₀.mapDerivedCategoryPlus.map
        (((Functor.mapDerivedCategoryPlusCompIso G₁ V).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso a ≪≫
          Functor.mapDerivedCategoryPlusCompIso U G₀).hom.app K) ≫
      (clopenLocalizedSquarePlus e₀).app
        (U.mapDerivedCategoryPlus.obj K) := by
  have hc := Functor.rightDerivedFunctorPlusBaseChange_cube G₁ H₁ G₀ H₀
    P₁ Q₁ P₀ Q₀ U V U' V' e e₀ a.hom b.hom c d h K
  rw [baseChange_eq_app G₁ Q₁ P₁ H₁,
    baseChange_eq_app H₁ V' U' H₀,
    baseChange_eq_app G₁ V U G₀,
    baseChange_eq_app G₀ Q₀ P₀ H₀] at hc
  rw [iso_square_eq H₁ V' U' H₀ b, iso_square_eq G₁ V U G₀ a] at hc
  simp only [Functor.map_comp, Category.assoc] at hc
  simp only [← V'.mapDerivedCategoryPlus.map_comp_assoc, Iso.inv_hom_id_app] at hc
  simp only [← Q₀.mapDerivedCategoryPlus.map_comp_assoc, Iso.inv_hom_id_app] at hc
  simp only [Functor.map_comp, Category.assoc] at hc
  dsimp only [Functor.comp_obj] at hc
  simp only [V'.mapDerivedCategoryPlus.map_id, Q₀.mapDerivedCategoryPlus.map_id,
    Category.id_comp] at hc
  have hn := H₀.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.naturality
    (((Functor.mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso d ≪≫
      Functor.mapDerivedCategoryPlusCompIso P₁ U').inv.app K)
  dsimp only [Functor.comp_obj] at hn
  rw [← hn] at hc
  have hn' := (((Functor.mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso c ≪≫
      Functor.mapDerivedCategoryPlusCompIso Q₁ V').inv).naturality
        (G₁.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn'
  rw [← reassoc_of% hn'] at hc
  apply (cancel_epi (V'.mapDerivedCategoryPlus.map
    (Q₁.mapDerivedCategoryPlus.map
      (G₁.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K)))).1
  apply (cancel_mono (H₀.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
    (P₀.mapDerivedCategoryPlus.obj (U.mapDerivedCategoryPlus.obj K)))).1
  simpa only [Category.assoc] using hc

end Cube

end ExactAlphaLocalization

private theorem derivedNatIso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusNatIso,
    Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, NatIso.mapHomologicalComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.refl_symm, Iso.refl_trans,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.ι_map, Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv,
    Iso.refl_inv, Functor.isoWhiskerLeft_inv, Category.id_comp]
  congr 2
  exact Category.comp_id _

namespace AlgebraicGeometry.ProEtale

private theorem proetale_alpha_factor
    (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)) :
    (cbcClopenAlphaSheaf Λ k i r p h).app F =
      (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback p i).flip).inv.app F ≫
      (finiteClopenProEtaleTail Λ k i r p h).app F := by
  simp only [cbcClopenAlphaSheaf, finiteClopenProEtaleTail, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  simp only [(openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
    (pullback.fst p i)).map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  rfl

private theorem sheaf_alpha_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
        ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app F) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) i).hom.app F) ≫
      (cbcClopenAlphaSheaf Λ k i r p h).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj F) := by
  rw [Etale.ClopenMateNormalization.alpha_app, Functor.map_comp]
  simp only [Category.assoc]
  have ht := finiteClopenTailSiteTransport Λ k i r p h F
  rw [ht]
  have hb := finiteClopenBetaSiteTransport Λ i p F
  dsimp only [Functor.comp_obj] at hb
  rw [reassoc_of% hb]
  rw [proetale_alpha_factor]

/-- Exact etale/pro-etale comparison respects the prescribed clopen alpha.
Source: Stacks Project, proetale.tex Tags 099R and 09AF, and more-etale.tex
Tag 0F7B (blueprint: lem-cbc-finite-clopen-alpha-site-transport).

Proof: write b and q for the projections of W ×_T S, and s for the clopen lift
of (k,r). First compare the inverse cartesian open base-change maps by transposing
under extension by zero along b. Both transposes are pullbacks of the open unit
along q followed by the cartesian inverse-image compositor. The canonical open
comparison carries this unit to the pro-etale unit, and pullback comparison respects
the compositor. Injectivity of transpose identifies these specific maps.

Next, on the disjoint opens s(V) and its complement in W ×_T S, the projection is
identity and zero respectively. The sheaf axiom for this two-member disjoint open
cover uniquely determines the projection. Comparison respects restriction and
extension by zero, so carries the etale projection to the pro-etale projection.
This includes empty images and empty complements, and does not require either
scheme to be Noetherian.

Compose these two equalities using compatibility of the canonical open-extension
and inverse-image compositors, including equality transport for s;b=k and s;q=r.
This proves the sheaf alpha equality. Apply the exact functors degreewise to
bounded-below complexes. The factorization identities for exact localization
identify the resulting transformation with the localized etale alpha and with
the right-derived-base-change definition of the pro-etale alpha. The universal
property of localization then gives the displayed equality on D+. This argument
compares chain maps before localization and does not assume that evaluation on
the derived category is faithful. No assertion about the proper mate is used. -/
theorem finiteClopenAlphaSiteTransport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ∀ (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryPlus.map
          ((Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h).app M) ≫
        (properOpenSiteExtensionIso Λ k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus.obj M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus Λ r).hom.app M) =
      (fixedComparisonPullbackPlus Λ p).hom.app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj M) ≫
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso Λ i).hom.app M) ≫
        (cbcClopenAlphaPlus Λ k i r p h).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategoryPlus.obj M) := by
  intro M
  have hc := ExactAlphaLocalization.cube
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) r)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) S)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W)
    (Etale.ClopenMateNormalization.alpha Λ k r p i h)
    (cbcClopenAlphaSheaf Λ k i r p h)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) i)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r)
    (sheaf_alpha_transport Λ k i r p h) M
  have he := ExactAlphaLocalization.baseChange_eq
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (cbcClopenAlphaSheaf Λ k i r p h)
  rw [← he] at hc
  simpa only [Etale.ClopenMateNormalization.derivedAlphaPlus_eq,
    fixedComparisonPullbackPlus, properOpenSiteExtensionIso, cbcClopenAlphaPlus,
    derivedNatIso_symm, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hc

end AlgebraicGeometry.ProEtale
