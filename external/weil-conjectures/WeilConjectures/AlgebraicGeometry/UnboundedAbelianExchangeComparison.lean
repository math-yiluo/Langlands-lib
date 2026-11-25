/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange

/-!
# Unbounded exchange and forgetting module coefficients

Source: Stacks Project, Tags 0D6J(3), 0D6E and 07A7
(auxiliary; not a blueprint node).

The inverse-image comparison is descended termwise. Its derived adjunction mate gives
an actual canonical direct-image comparison; the theorem asserts its invertibility and
its normalization by the right-derived units. This normalization identifies it with
0D6J's K-injective replacement construction, without preservation of K-injectives.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Exact localization comparisons, normalized on the homotopy category.
private lemma exactComparison_factorsh
    {C D E Z : Type*} [Category* C] [Category* D] [Category* E] [Category* Z]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory Z]
    (F : C ⥤ D) (G : D ⥤ Z) (F' : C ⥤ E) (G' : E ⥤ Z)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso F' G').symm).hom.app (DerivedCategory.Qh.obj P) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactorsh.hom.app P) ≫
        G'.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fach F' G' P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [hc, Functor.mapDerivedCategoryNatIso_fach]
  have hc := Functor.mapDerivedCategoryCompIso_fach F G P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [← hc]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

private lemma homotopyCompIso_inv_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ :=
  congrArg Iso.inv (Iso.ext
    (Functor.mapHomotopyCategoryCompIso_refl_hom_app (.up ℤ) F G K) :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app K = Iso.refl _)

private lemma exactComparison_inv
    {C D E Z : Type*} [Category* C] [Category* D] [Category* E] [Category* Z]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory Z]
    (F : C ⥤ D) (G : D ⥤ Z) (F' : C ⥤ E) (G' : E ⥤ Z)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso F' G').symm).inv =
    (Functor.mapDerivedCategoryCompIso F' G' ≪≫
      Functor.mapDerivedCategoryNatIso e.symm ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm).hom := by
  have hi : (Functor.mapDerivedCategoryNatIso e).inv =
      (Functor.mapDerivedCategoryNatIso e.symm).hom := rfl
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, hi, Category.assoc]

-- K-injective derivability makes these right derived functors absolute.
private lemma derivedSquare_absolute
    {B C E : Type*} [Category* B] [Category* C] [Category* E]
    [Abelian B] [Abelian C] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B] (F : B ⥤ C) [F.Additive]
    (T : DerivedCategory C ⥤ E) :
    (F.rightDerivedFunctor ⋙ T).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorUnit T ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso B (.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism B)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

attribute [local instance] derivedSquare_absolute

section DerivedSquare

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

-- The comparison before right-derived descent; only beta and gamma are exact.
private noncomputable def derivedSquareAux (e : G ⋙ γ ⟶ β ⋙ G') :
    (G.mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh ⋙ γ.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ β.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) γ.mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ γ)) (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e (.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (β ⋙ G')) (.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (β.mapHomotopyCategory (.up ℤ)) G'.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight β.mapDerivedCategoryFactorsh.inv G'.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

private noncomputable def derivedSquare (e : G ⋙ γ ⟶ β ⋙ G') :
    G.rightDerivedFunctor ⋙ γ.mapDerivedCategory ⟶
      β.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  (G.rightDerivedFunctor ⋙ γ.mapDerivedCategory).rightDerivedDesc
    (Functor.whiskerRight G.rightDerivedFunctorUnit γ.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso B (.up ℤ)) _ (derivedSquareAux e)

@[reassoc]
private lemma derivedSquare_fac (e : G ⋙ γ ⟶ β ⋙ G') :
    (Functor.whiskerRight G.rightDerivedFunctorUnit γ.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft DerivedCategory.Qh (derivedSquare e) =
    derivedSquareAux e :=
  Functor.rightDerived_fac _ _ _ _ _

private lemma derivedSquare_app_fac (e : G ⋙ γ ⟶ β ⋙ G')
    (K : HomotopyCategory B (.up ℤ)) :
    γ.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        γ.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app K) ≫
        (derivedSquare e).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K) ≫
        G'.rightDerivedFunctorUnit.app ((β.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G'.rightDerivedFunctor.map (β.mapDerivedCategoryFactorsh.inv.app K) := by
  have h := congr_app (derivedSquare_fac e) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at h
  have hh := congrArg (fun k ↦
    γ.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫ k) h
  simp only [derivedSquareAux, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hh
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    homotopyCompIso_inv_app] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at hh
  erw [Category.id_comp, Category.id_comp] at hh
  erw [Iso.inv_hom_id_app_assoc] at hh
  exact hh

-- Test invertibility on module K-injectives; beta need not preserve K-injectives.
private lemma derivedSquare_isIso (e : G ⋙ γ ≅ β ⋙ G')
    (hβ : ∀ (K : CochainComplex B ℤ) [K.IsKInjective],
      IsIso (G'.rightDerivedFunctorUnit.app
        ((β.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)))) :
    IsIso (derivedSquare e.hom) := by
  have ht : (β.mapDerivedCategory ⋙ G'.rightDerivedFunctor).IsRightDerivedFunctor
      (derivedSquareAux e.hom) (HomotopyCategory.quasiIso B (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((G.mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh ⋙
        γ.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun I ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
    change IsIso ((derivedSquareAux e.hom).app
      ((HomotopyCategory.quotient _ _).obj K))
    let eh : (G ⋙ γ).mapHomotopyCategory (.up ℤ) ≅
        (β ⋙ G').mapHomotopyCategory (.up ℤ) :=
      { hom := NatTrans.mapHomotopyCategory e.hom _
        inv := NatTrans.mapHomotopyCategory e.inv _
        hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
    have : IsIso (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) :=
      ⟨⟨eh.inv, eh.hom_inv_id, eh.inv_hom_id⟩⟩
    have := hβ K
    simp only [derivedSquareAux, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _
    (HomotopyCategory.quasiIso B (.up ℤ)) _ (derivedSquareAux e.hom)).1 ht

end DerivedSquare

section DerivedCube

private lemma exactComparison_inv_factorsh
    {X Y Y' Z : Type*} [Category* X] [Category* Y] [Category* Y'] [Category* Z]
    [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
    [HasDerivedCategory X] [HasDerivedCategory Y]
    [HasDerivedCategory Y'] [HasDerivedCategory Z]
    (F : X ⥤ Y) (J : Y ⥤ Z) (F' : X ⥤ Y') (J' : Y' ⥤ Z)
    [F.Additive] [J.Additive] [F'.Additive] [J'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (t : F ⋙ J ≅ F' ⋙ J') (M : HomotopyCategory X (.up ℤ)) :
    J'.mapDerivedCategoryFactorsh.inv.app ((F'.mapHomotopyCategory (.up ℤ)).obj M) ≫
      D(J').map (F'.mapDerivedCategoryFactorsh.inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F J ≪≫ Functor.mapDerivedCategoryNatIso t ≪≫
        (Functor.mapDerivedCategoryCompIso F' J').symm).inv.app (DerivedCategory.Qh.obj M) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory t.inv (.up ℤ)).app M) ≫
      J.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj M) ≫
      D(J).map (F.mapDerivedCategoryFactorsh.inv.app M) := by
  let A := D(J).mapIso (F.mapDerivedCategoryFactorsh.app M) ≪≫
    J.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (.up ℤ)).obj M)
  let A' := D(J').mapIso (F'.mapDerivedCategoryFactorsh.app M) ≪≫
    J'.mapDerivedCategoryFactorsh.app ((F'.mapHomotopyCategory (.up ℤ)).obj M)
  let r : ((F ⋙ J).mapHomotopyCategory (.up ℤ)) ≅ ((F' ⋙ J').mapHomotopyCategory (.up ℤ)) :=
    { hom := NatTrans.mapHomotopyCategory t.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory t.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have hi : ((Functor.mapDerivedCategoryCompIso F J ≪≫
      Functor.mapDerivedCategoryNatIso t ≪≫ (Functor.mapDerivedCategoryCompIso F' J').symm).app
        (DerivedCategory.Qh.obj M)) ≪≫ A' =
      A ≪≫ DerivedCategory.Qh.mapIso (r.app M) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      A, A', r, Category.assoc] using exactComparison_factorsh F J F' J' t M
  simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    A, A', r, Category.assoc] using congrArg Iso.inv hi

variable {B C B' C' B₀ C₀ B₀' C₀' : Type*}
  [Category* B] [Category* C] [Category* B'] [Category* C']
  [Category* B₀] [Category* C₀] [Category* B₀'] [Category* C₀']
  [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

-- The ordinary cube descends by the normalization equations and derived uniqueness.
private lemma derivedSquare_cube
    (e : G ⋙ Q ⟶ P ⋙ H) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G ⋙ V ⟶ U ⋙ G₀) (b : H ⋙ V' ⟶ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q ⋙ V') (d : U ⋙ P₀ ≅ P ⋙ U')
    (h : ∀ F : B, V'.map (e.app F) ≫ b.app (P.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G.obj F) ≫ Q₀.map (a.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory B) :
    D(V').map ((derivedSquare e).app K) ≫
        (derivedSquare b).app (D(P).obj K) ≫
        R(H₀).map ((Functor.mapDerivedCategoryCompIso U P₀ ≪≫
          Functor.mapDerivedCategoryNatIso d ≪≫
          (Functor.mapDerivedCategoryCompIso P U').symm).inv.app K) =
      (Functor.mapDerivedCategoryCompIso V Q₀ ≪≫
        Functor.mapDerivedCategoryNatIso c ≪≫ (Functor.mapDerivedCategoryCompIso Q V').symm).inv.app
          (R(G).obj K) ≫
        D(Q₀).map ((derivedSquare a).app K) ≫
        (derivedSquare e₀).app (D(U).obj K) := by
  let dc := Functor.mapDerivedCategoryCompIso V Q₀ ≪≫
    Functor.mapDerivedCategoryNatIso c ≪≫ (Functor.mapDerivedCategoryCompIso Q V').symm
  let dd := Functor.mapDerivedCategoryCompIso U P₀ ≪≫
    Functor.mapDerivedCategoryNatIso d ≪≫ (Functor.mapDerivedCategoryCompIso P U').symm
  let α : R(G) ⋙ (D(Q) ⋙ D(V')) ⟶ (D(U) ⋙ D(P₀)) ⋙ R(H₀) :=
    Functor.whiskerRight (derivedSquare e) D(V') ≫
    Functor.whiskerLeft D(P) (derivedSquare b) ≫
    Functor.whiskerRight dd.inv R(H₀)
  let β : R(G) ⋙ (D(Q) ⋙ D(V')) ⟶ (D(U) ⋙ D(P₀)) ⋙ R(H₀) :=
    Functor.whiskerLeft R(G) dc.inv ≫
    Functor.whiskerRight (derivedSquare a) D(Q₀) ≫
    Functor.whiskerLeft D(U) (derivedSquare e₀)
  -- Absoluteness reduces equality to compatibility on the homotopy category.
  have heq : α = β := by
    apply CategoryTheory.Functor.rightDerived_ext (R(G) ⋙ (D(Q) ⋙ D(V')))
      (Functor.whiskerRight G.rightDerivedFunctorUnit (D(Q) ⋙ D(V')) ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso B (.up ℤ))
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp,
      Functor.comp_map, α, β, Category.assoc]
    -- Replace the first two derived faces by their defining unit factorizations.
    have he := congr_app (derivedSquare_fac e) M
    have ha := congr_app (derivedSquare_fac a) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at he ha
    rw [← D(V').map_comp_assoc, he]
    have hc := dc.inv.naturality (G.rightDerivedFunctorUnit.app M)
    simp only [Functor.comp_map] at hc
    rw [reassoc_of% hc, ← D(Q₀).map_comp_assoc, ha]
    simp only [derivedSquareAux, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc]
    -- Move the localization comparisons through the remaining faces and factor them.
    have hb := (derivedSquare b).naturality
      (P.mapDerivedCategoryFactorsh.inv.app M)
    have he₀ := (derivedSquare e₀).naturality
      (U.mapDerivedCategoryFactorsh.inv.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hb he₀
    rw [reassoc_of% hb, he₀]
    have hbf := congr_app (derivedSquare_fac b)
      ((P.mapHomotopyCategory (.up ℤ)).obj M)
    have he₀f := congr_app (derivedSquare_fac e₀)
      ((U.mapHomotopyCategory (.up ℤ)).obj M)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at hbf he₀f
    rw [reassoc_of% hbf, reassoc_of% he₀f]
    simp only [derivedSquareAux, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc]
    simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      homotopyCompIso_inv_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_obj]
    have hv := V'.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory e (.up ℤ)).app M)
    have hq := Q₀.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory a (.up ℤ)).app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hv hq
    erw [reassoc_of% hv, reassoc_of% hq]
    -- Express the two exact edges by their termwise comparisons.
    have hd := exactComparison_inv_factorsh U P₀ P U' d M
    change U'.mapDerivedCategoryFactorsh.inv.app ((P.mapHomotopyCategory (.up ℤ)).obj M) ≫
      D(U').map (P.mapDerivedCategoryFactorsh.inv.app M) ≫
      dd.inv.app (DerivedCategory.Qh.obj M) = _ at hd
    rw [← R(H₀).map_comp, ← R(H₀).map_comp, hd]
    simp only [Functor.map_comp]
    have hn := H₀.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory d.inv (.up ℤ)).app M)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hcf := exactComparison_factorsh V Q₀ Q V' c ((G.mapHomotopyCategory (.up ℤ)).obj M)
    have hci : dc.inv.app (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        D(Q₀).map (V.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        Q₀.mapDerivedCategoryFactorsh.hom.app
          ((V.mapHomotopyCategory (.up ℤ)).obj ((G.mapHomotopyCategory (.up ℤ)).obj M)) =
      D(V').map (Q.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        V'.mapDerivedCategoryFactorsh.hom.app
          ((Q.mapHomotopyCategory (.up ℤ)).obj ((G.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.inv (.up ℤ)).app
          ((G.mapHomotopyCategory (.up ℤ)).obj M)) := by
      apply (cancel_epi (dc.hom.app
        (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj M)))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      erw [Category.assoc, Category.assoc, reassoc_of% hcf]
      simp only [← DerivedCategory.Qh.map_comp,
        ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
        Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    erw [reassoc_of% hci]
    -- The resulting termwise composites are equal by the underived cube hypothesis.
    let l : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerRight e V' ≫ Functor.whiskerLeft P b ≫ Functor.whiskerRight d.inv H₀
    let r : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerLeft G c.inv ≫ Functor.whiskerRight a Q₀ ≫ Functor.whiskerLeft U e₀
    have hlr : l = r := by
      apply NatTrans.ext
      funext F
      exact h F
    have hh : (V'.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e (.up ℤ)).app M) ≫
          (NatTrans.mapHomotopyCategory b (.up ℤ)).app ((P.mapHomotopyCategory (.up ℤ)).obj M) ≫
          (H₀.mapHomotopyCategory (.up ℤ)).map
            ((NatTrans.mapHomotopyCategory d.inv (.up ℤ)).app M) =
        (NatTrans.mapHomotopyCategory c.inv (.up ℤ)).app ((G.mapHomotopyCategory (.up ℤ)).obj M) ≫
          (Q₀.mapHomotopyCategory (.up ℤ)).map
            ((NatTrans.mapHomotopyCategory a (.up ℤ)).app M) ≫
          (NatTrans.mapHomotopyCategory e₀ (.up ℤ)).app
            ((U.mapHomotopyCategory (.up ℤ)).obj M) := by
      have ht := congr_app
        (congrArg (fun k ↦ NatTrans.mapHomotopyCategory k (.up ℤ)) hlr) M
      simp only [l, r, NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at ht
      exact ht
    have hqh := congrArg DerivedCategory.Qh.map hh
    simp only [Functor.map_comp] at hqh
    erw [reassoc_of% hqh]
    rfl
  simpa [α, β, dc, dd] using congr_app heq K

end DerivedCube

private lemma mate_eq_of_unit
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' H) (τ : R ⋙ G ⟶ H ⋙ R')
    (hu : ∀ M : C, adj'.unit.app (G.obj M) ≫ R'.map (σ.app M) =
      G.map (adj.unit.app M) ≫ τ.app (L.obj M)) :
    (mateEquiv adj adj' σ) = τ := by
  apply NatTrans.ext
  funext N
  simp only [mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  change adj'.unit.app (G.obj (R.obj N)) ≫
      R'.map (σ.app (R.obj N)) ≫
        R'.map (H.map (adj.counit.app N)) = τ.app N
  rw [← Category.assoc]
  rw [hu, Category.assoc]
  erw [← τ.naturality]
  simp only [Functor.comp_map, ← G.map_comp_assoc, adj.right_triangle_components]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

section DerivedMates

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [Abelian.HasKInjectiveResolutions C₁] [Abelian.HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [Abelian.HasKInjectiveResolutions C₁] [Abelian.HasKInjectiveResolutions C₃]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
private lemma homotopy_mate_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') (K : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K =
      (adj'.mapHomotopyCategory (.up ℤ)).unit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app
            ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((G'.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C₄ (.up ℤ)).map _ =
    (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₄ (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map]
  exact congrArg (fun t ↦ _ ≫ _ ≫ t) (Category.comp_id _)

-- Compute the derived mate using the fixed derived unit/counit normalization.
private lemma derived_mate_app_fac (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      G'.mapDerivedCategory)
    (hθ : ∀ N : HomotopyCategory C₂ (.up ℤ),
      θ.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N))
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app
          (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) := by
  have hmate : ∀ (Z : DerivedCategory C₁),
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app Z =
        adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
            (G.mapDerivedCategory.obj (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (θ.app (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (G'.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app Z)) := fun Z => by
    simp [mateEquiv_apply]
  set N := (R.mapHomotopyCategory (.up ℤ)).obj K
  set u := R.rightDerivedFunctorUnit.app K
  have h₁ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map u)
  have h₂ := θ.naturality u
  have h₃ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit K
  change L.mapDerivedCategory.map u ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj K) =
    _ at h₃
  have h₄ := homotopy_mate_app adj adj' σ K
  have h₅ := R'.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N ≫
      (G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K))
  have h₆ := (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C₄ (.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
    R'.rightDerivedFunctorUnit ((G.mapHomotopyCategory (.up ℤ)).obj N)
  change adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj N)) ≫ _ = _ at h₆
  have h₇ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategoryFactorsh.hom.app N)
  have h₈ := hθ N
  have h₉ := G'.mapDerivedCategoryFactorsh.hom.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₅ h₇ h₉
  rw [hmate, reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp (G'.mapDerivedCategory), h₃, h₄]
  erw [← Functor.map_comp (R'.mapHomotopyCategory (.up ℤ))]
  erw [Functor.map_comp DerivedCategory.Qh, Category.assoc, reassoc_of% h₅]
  erw [← reassoc_of% h₆, reassoc_of% h₇]
  congr 1
  have key : θ.app (DerivedCategory.Qh.obj N) ≫
      G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N) ≫
        DerivedCategory.Qh.map
          ((G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) ≫
        G'.mapDerivedCategoryFactorsh.inv.app K := by
    rw [← cancel_mono (G'.mapDerivedCategoryFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    rw [h₉, reassoc_of% h₈]
    erw [Category.comp_id]
  rw [key]
  simp only [Functor.map_comp]
  simp only [Category.assoc]

private lemma derived_mate_eq_square (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      G'.mapDerivedCategory)
    (hθ : ∀ N : HomotopyCategory C₂ (.up ℤ),
      θ.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N)) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction θ) =
        derivedSquare (mateEquiv adj adj' σ) := by
  apply Functor.rightDerived_ext (R.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (Functor.whiskerRight R.rightDerivedFunctorUnit G.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  apply NatTrans.ext
  funext K
  have hn := derived_mate_app_fac adj adj' σ θ hθ K
  have hd := congr_app (derivedSquare_fac (mateEquiv adj adj' σ)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hd ⊢
  rw [hd]
  simp only [derivedSquareAux, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    homotopyCompIso_inv_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp]
  simpa only [Category.assoc] using hn

private lemma derived_mate_exact_eq_square (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : G ⋙ L' ≅ L ⋙ G') :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ ((Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso L G').symm).hom))) =
      derivedSquare (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) := by
  apply derived_mate_eq_square
  intro N
  exact exactComparison_factorsh G L' L G' e N

private lemma derived_mate_exact_inv_eq_square (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : L ⋙ G' ≅ G ⋙ L') :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ ((Functor.mapDerivedCategoryCompIso L G' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso G L').symm).inv))) =
      derivedSquare (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.inv)) := by
  apply derived_mate_eq_square
  intro N
  have hi : (Functor.mapDerivedCategoryNatIso e).inv =
      (Functor.mapDerivedCategoryNatIso e.symm).hom := by rfl
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, TwoSquare.mk, hi, Category.assoc] using
    exactComparison_factorsh G L' L G' e.symm N

end DerivedMates

/-- The termwise inverse-image coefficient comparison, transported to exact inverse image.
Source: Stacks Project, Tags 03D3 and 07A7
(auxiliary; not a blueprint node). -/
noncomputable def moduleAbelianUnboundedUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B) :
    D((v)^*[ModuleCat.{u + 1} Λ]) ⋙ D(moduleAbelianForget Λ A) ≅
      D(moduleAbelianForget Λ B) ⋙ D((v)^*[AddCommGrpCat.{u + 1}]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleAbelianUpperStarIso Λ v).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The adjunction mate of the termwise inverse-image comparison. Its right-derived-unit
normalization below identifies it with the map computed by a module K-injective complex
and an abelian K-injective replacement of its underlying complex.
Source: Stacks Project, Tags 0D6J(3) and 07A7
(auxiliary; not a blueprint node). -/
noncomputable def moduleAbelianUnboundedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B) :
    R((v)_*[ModuleCat.{u + 1} Λ]) ⋙ D(moduleAbelianForget Λ B) ⟶
      D(moduleAbelianForget Λ A) ⋙ R((v)_*[AddCommGrpCat.{u + 1}]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v)
    (TwoSquare.mk _ _ _ _ (moduleAbelianUnboundedUpperStarIso Λ v).inv))

-- Naturality transfers the unit isomorphism across an acyclic replacement.
private lemma unit_isIso_of_resolution_quasiIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (P : CochainComplex C ℤ)
    (h : ∀ (J : CochainComplex C ℤ) [J.IsKInjective] (j : P ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P)) := by
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective P
  have := hJ
  have := hj
  have := h J j
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hq : IsIso (DerivedCategory.Qh.map (q.map j)) := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map j)
    rw [NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C)]
    infer_instance
  have hg : IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (q.map j))) := by
    change IsIso ((HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((G.mapHomologicalComplex (.up ℤ)).map j))
    rw [NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D)]
    infer_instance
  have hn := G.rightDerivedFunctorUnit.naturality (q.map j)
  dsimp only [Functor.comp_map] at hn
  have : IsIso (G.rightDerivedFunctorUnit.app (q.obj P) ≫
      G.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map j))) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (G.rightDerivedFunctorUnit.app (q.obj P))
    (G.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map j)))

private lemma exactFunctor_reflects_derived
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro K L h hh
  rw [DerivedCategory.isIso_iff]
  intro i
  have hi : IsIso (F.map ((DerivedCategory.homologyFunctor C i).map h)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) h).2
      (by change IsIso ((DerivedCategory.homologyFunctor D i).map
        (F.mapDerivedCategory.map h)); infer_instance)
  exact isIso_of_reflects_iso _ F

/-- Exact conservative coefficient forgetting intertwines canonical unbounded exchange.
The unit equation is stated on every homotopy complex: on a K-injective module complex
`I`, apply it and naturality of the abelian derived unit to a quasi-isomorphism `UI → J`
with `J` abelian K-injective. Both derived units at K-injectives are invertible, so the
equation says exactly that the comparison is the class of `v_* UI → v_* J`.

Source: Stacks Project, Tags 0D6J(3), 0D6E and 07A7
(auxiliary; not a blueprint node).

Proof:
1. Forgetting preserves kernels and sheafified cokernels. The inverse of a bijective
module map is linear. Exact-functor localization and its homology comparison imply
exactness and reflection of isomorphisms on unbounded derived categories.
2. Descend the ordinary inverse-image coefficient comparison termwise. Its square
coherence follows degree by degree and survives localization.
3. Descend the sectionwise direct-image comparison using the absolute right-derived
functor property supplied by K-injective resolutions. Its defining unit equation holds
on every homotopy complex. The acyclicity statement of Tag 0D6J(3), isolated in
`moduleAbelianForget_kInjective_directImage_quasiIso`, makes the abelian derived unit
invertible on forgotten module K-injectives. The derivability criterion therefore
makes the descended comparison invertible.
4. Compute the derived adjunction mate on homotopy complexes using the explicit
normalizations of the derived unit and counit. It has the same unit equation as the
descended comparison; uniqueness of right-derived descent identifies the two maps.
5. The ordinary module/abelian exchange identity is already proved. Pass its cube of
natural transformations to homotopy categories, insert the exact-functor factorization
isomorphisms, and use the defining unit equations of the four descended comparisons.
Right-derived uniqueness gives the cube equality on the derived category. Step 4
identifies its four faces with the fixed mate definitions in the statement.
-/
theorem unbounded_abelian_exchange_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    (∀ T : Scheme.{u},
      PreservesFiniteLimits (moduleAbelianForget Λ T) ∧
      PreservesFiniteColimits (moduleAbelianForget Λ T) ∧
      (D(moduleAbelianForget Λ T)).IsTriangulated ∧
      (D(moduleAbelianForget Λ T)).ReflectsIsomorphisms ∧
      ∀ i : ℤ, Nonempty
        (D(moduleAbelianForget Λ T) ⋙
            DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) i ≅
          DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i ⋙
            moduleAbelianForget Λ T)) ∧
    (∀ {A B : Scheme.{u}} (v : A ⟶ B),
      IsIso (moduleAbelianUnboundedLowerStarComparison Λ v) ∧
      ∀ P : HomotopyCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (ComplexShape.up ℤ),
        (moduleAbelianForget Λ B).mapDerivedCategoryFactorsh.inv.app
            (((v)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj P) ≫
          D(moduleAbelianForget Λ B).map
            (((v)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorUnit.app P) ≫
          (moduleAbelianUnboundedLowerStarComparison Λ v).app
            (DerivedCategory.Qh.obj P) =
        ((v)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorUnit.app
            ((moduleAbelianForget Λ A).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj P) ≫
          R((v)_*[AddCommGrpCat.{u + 1}]).map
            ((moduleAbelianForget Λ A).mapDerivedCategoryFactorsh.inv.app P)) ∧
    ∀ K : DerivedCategoryModule Λ X,
      D(moduleAbelianForget Λ Y').map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
        (moduleAbelianUnboundedLowerStarComparison Λ f').app
          (D((g')^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R((f')_*[AddCommGrpCat.{u + 1}]).map
          ((moduleAbelianUnboundedUpperStarIso Λ g').hom.app K) =
      (moduleAbelianUnboundedUpperStarIso Λ g).hom.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        D((g)^*[AddCommGrpCat.{u + 1}]).map
          ((moduleAbelianUnboundedLowerStarComparison Λ f).app K) ≫
        (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D(moduleAbelianForget Λ X).obj K) := by
  have hm {A B : Scheme.{u}} (v : A ⟶ B) :=
    mate_eq_of_unit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v)
      (TwoSquare.mk _ _ _ _ (moduleAbelianUpperStarIso Λ v).hom)
      (moduleAbelianLowerStarIso Λ v).hom (fun M ↦ by
        change _ = (moduleAbelianForget Λ B).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app M) ≫ 𝟙 _
        rw [Category.comp_id]
        exact (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv
          _ _ |>.apply_symm_apply _)
  have hc {A B : Scheme.{u}} (v : A ⟶ B) :
      moduleAbelianUnboundedLowerStarComparison Λ v =
        derivedSquare (moduleAbelianLowerStarIso Λ v).hom := by
    have h := derived_mate_exact_inv_eq_square
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v)
      (moduleAbelianUpperStarIso Λ v).symm
    simpa only [Iso.symm_inv, hm,
      moduleAbelianUnboundedLowerStarComparison, moduleAbelianUnboundedUpperStarIso,
      mapDerivedUpperStarLowerStarAdjunction] using h
  refine ⟨?_, ?_, ?_⟩
  · intro T
    refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · exact exactFunctor_reflects_derived (moduleAbelianForget Λ T)
    · intro i
      exact ⟨((moduleAbelianForget Λ T).mapDerivedCategoryHomologyFunctorIso i).symm⟩
  · intro A B v
    refine ⟨?_, ?_⟩
    · rw [hc]
      apply derivedSquare_isIso
      intro I hI
      apply unit_isIso_of_resolution_quasiIso ((v)_*[AddCommGrpCat.{u + 1}])
        (((moduleAbelianForget Λ A).mapHomologicalComplex (.up ℤ)).obj I)
      intro J hJ j hj
      exact moduleAbelianForget_kInjective_directImage_quasiIso Λ v I J j
    · intro P
      rw [hc]
      have h := derivedSquare_app_fac (moduleAbelianLowerStarIso Λ v).hom P
      simpa only [moduleAbelianLowerStarIso, Iso.refl_hom,
        NatTrans.mapHomotopyCategory_id, NatTrans.id_app,
        CategoryTheory.Functor.map_id, Category.id_comp] using h
  · intro K
    have h := derivedSquare_cube
      ((f)_*[ModuleCat.{u + 1} Λ]) ((f')_*[ModuleCat.{u + 1} Λ])
      ((f)_*[AddCommGrpCat.{u + 1}]) ((f')_*[AddCommGrpCat.{u + 1}])
      ((g')^*[ModuleCat.{u + 1} Λ]) ((g)^*[ModuleCat.{u + 1} Λ])
      ((g')^*[AddCommGrpCat.{u + 1}]) ((g)^*[AddCommGrpCat.{u + 1}])
      (moduleAbelianForget Λ X) (moduleAbelianForget Λ Y)
      (moduleAbelianForget Λ X') (moduleAbelianForget Λ Y')
      (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)
      (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)
      (moduleAbelianLowerStarIso Λ f).hom (moduleAbelianLowerStarIso Λ f').hom
      (moduleAbelianUpperStarIso Λ g) (moduleAbelianUpperStarIso Λ g')
      (moduleAbelianUnderivedExchange_compatibility Λ sq.toCommSq) K
    have he (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
        [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
        exactDerivedBaseChangeMap A sq.toCommSq =
          derivedSquare (baseChangeMap A sq.toCommSq) :=
      derived_mate_exact_eq_square (upperStarLowerStarAdjunction A f)
        (upperStarLowerStarAdjunction A f') (squareUpperStarIso A sq.toCommSq)
    rw [he (ModuleCat.{u + 1} Λ), he AddCommGrpCat.{u + 1}, hc f, hc f']
    rw [exactComparison_inv, exactComparison_inv] at h
    exact h

end AlgebraicGeometry.Etale
