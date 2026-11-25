/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeEncodingPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-! Comparison of total derived and exact condensed exchange.
Source: blueprint rational proper-base-change proof, exact derived factorization.
(blueprint: lem-sf-total-derived-exchange-exact-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  Mod.monoidalClosed Mod.monoidalCategoryStruct

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Mod.monoidalCategory
  Functor.mapDerivedCategoryNatIso
  CondensedRing.upperStar CondensedRing.lowerStar
/-- The exchange mate formed from exact condensed pullback on the derived category.
Source: blueprint rational proper-base-change proof, exact derived factorization.
(blueprint: lem-sf-total-derived-exchange-exact-comparison). -/
@[irreducible] def exactCondensedExchange (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :=
  (mateEquiv
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso
        (NativeEncoding.condensedPullbackSquare l sq)).hom))

/-- The ordinary condensed pullback square for an arbitrary commutative coefficient.
Source: canonical pullback compositors in the rational base-change argument.
(blueprint: lem-sf-total-derived-exchange-exact-comparison). -/
@[irreducible] def condensedPullbackSquareFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ p' ≅
      CondensedRing.upperStar Λ p ⋙ CondensedRing.upperStar Λ v :=
  (CondensedRing.upperStarComp Λ p' g).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w.symm) ≪≫
      CondensedRing.upperStarComp Λ v p

/-- The exchange mate formed from exact condensed pullback on the derived category.
Source: blueprint rational proper-base-change proof, exact derived factorization.
(blueprint: lem-sf-total-derived-exchange-exact-comparison). -/
@[irreducible] def exactCondensedExchangeFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :=
  (mateEquiv
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso
        (condensedPullbackSquareFor Λ sq)).hom))

private theorem transported_mate_id
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R) (e : F' ≅ F) :
    (mateEquiv (a.ofNatIsoLeft e.symm) a
      (TwoSquare.mk (𝟭 C) F' F (𝟭 D) e.inv)) = 𝟙 R := by
  apply NatTrans.ext
  funext N
  simp only [mateEquiv_apply, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    TwoSquare.mk, Functor.comp_obj, Functor.id_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.id_map, Functor.comp_map, Iso.symm_inv, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_comp, NatTrans.id_app]
  rw [← R.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact a.right_triangle_components N

private theorem total_adjunction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.derivedUpperStarLowerStarAdjunction Λ f =
      Adjunction.ofNatIsoLeft
        (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
  exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    ((CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

private theorem total_mate_id
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
      (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk (𝟭 _) _ _ (𝟭 _)
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv)) =
      𝟙 (CondensedRing.moduleObjectDerivedPushforward Λ f) := by
  rw [total_adjunction_eq]
  exact transported_mate_id _ _

private theorem total_comp_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
        ((CondensedRing.moduleObjectDerivedPullback Λ g).obj M) ≫
      (CondensedRing.upperStar Λ f).mapDerivedCategory.map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app M) =
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
        (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
          (CondensedRing.upperStar Λ f)).symm).hom.app M := by
  simp only [CondensedRing.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    CondensedRing.moduleObjectDerivedPullback, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem invert_compositor
    {C : Type*} [Category C] {A B C' D : C}
    (a : A ≅ B) (b : C' ≅ D) (x : A ⟶ C') (y : B ⟶ D)
    (h : a.hom ≫ y = x ≫ b.hom) : a.inv ≫ x = y ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem invert_square
    {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ≅ B) (b : B ≅ C') (c : D ≅ E) (d : E ≅ F)
    (x : A ⟶ D) (y : C' ⟶ F)
    (h : a.hom ≫ b.hom ≫ y = x ≫ c.hom ≫ d.hom) :
    b.inv ≫ a.inv ≫ x = y ≫ d.inv ≫ c.inv := by
  have he := invert_compositor (a ≪≫ b) (c ≪≫ d) x y
    (by simpa only [Iso.trans_hom, Category.assoc] using h)
  simpa only [Iso.trans_inv, Category.assoc] using he

@[irreducible] private def exactComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)).symm

private theorem exactComp_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (exactComp Λ f g).hom =
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)).inv := by
  delta exactComp
  rfl

private theorem total_inverse_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (CondensedRing.leftDerivedUpperStarComp Λ f g).inv.app M ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)).hom.app M =
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
        ((CondensedRing.moduleObjectDerivedPullback Λ g).obj M) ≫
      (CondensedRing.upperStar Λ f).mapDerivedCategory.map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app M) ≫
      (exactComp Λ f g).inv.app M := by
  unfold exactComp
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using
    invert_compositor ((CondensedRing.leftDerivedUpperStarComp Λ f g).app M)
      ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
        (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
          (CondensedRing.upperStar Λ f)).symm).app M) _ _ (total_comp_normalization Λ f g M)

private theorem derived_eqToIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (CondensedRing.upperStar Λ) h))).hom =
    (eqToIso (congrArg (fun t ↦ (CondensedRing.upperStar Λ t).mapDerivedCategory) h)).hom := by
  subst g
  exact Functor.mapDerivedCategoryNatIso_refl

section DerivedPaste
variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  {J K : A ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
private theorem derived_paste_square (a : J ≅ F₁ ⋙ F₂) (b : J ≅ K)
    (c : K ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso (a.symm ≪≫ b ≪≫ c)).hom =
      (Functor.mapDerivedCategoryNatIso a ≪≫
        (Functor.mapDerivedCategoryCompIso F₁ F₂).symm).inv ≫
      (Functor.mapDerivedCategoryNatIso b).hom ≫
      (Functor.mapDerivedCategoryNatIso c ≪≫
        (Functor.mapDerivedCategoryCompIso G₁ G₂).symm).hom := by
  simp only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
end DerivedPaste

private theorem exact_square_normalizationFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    ((exactComp Λ p' g).symm ≪≫
      eqToIso (congrArg
        (fun t : X' ⟶ Y ↦ (CondensedRing.upperStar
          Λ t).mapDerivedCategory) sq.w.symm) ≪≫
      exactComp Λ v p).hom =
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor Λ sq)).hom := by
  have h := derived_paste_square
    (CondensedRing.upperStarComp Λ p' g)
    (eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w.symm))
    (CondensedRing.upperStarComp Λ v p)
  rw [derived_eqToIso Λ sq.w.symm] at h
  simpa only [exactComp, condensedPullbackSquareFor,
    Iso.trans_hom, Iso.symm_hom] using h.symm

private theorem paste_three
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ F) (e : F ⟶ D)
    (x : B ⟶ G) (y : D ⟶ H) (z : G ⟶ H)
    {I J K : C} (k : G ⟶ I) (l : I ⟶ J) (m : J ⟶ K) (n : H ⟶ K)
    (h₁ : a ≫ b = c ≫ d ≫ e) (he : x ≫ z = b ≫ y)
    (h₂ : k ≫ l ≫ m = z ≫ n) :
    c ≫ d ≫ e ≫ y ≫ n = a ≫ x ≫ k ≫ l ≫ m := by
  rw [← reassoc_of% h₁, ← reassoc_of% he, ← h₂]

attribute [local irreducible]
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

private theorem total_comparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (eqToIso (congrArg (CondensedRing.moduleObjectDerivedPullback Λ) h)).hom.app M ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app M =
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app M ≫
      (eqToIso (congrArg (fun t ↦
        (CondensedRing.upperStar Λ t).mapDerivedCategory) h)).hom.app M := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

attribute [local irreducible] CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

private theorem totalSquare_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    (CondensedRing.moduleObjectDerivedPullbackSquareComparison Λ sq).hom =
      (CondensedRing.leftDerivedUpperStarComp Λ p' g).inv ≫
        (eqToIso (congrArg (CondensedRing.moduleObjectDerivedPullback Λ) sq.w.symm)).hom ≫
        (CondensedRing.leftDerivedUpperStarComp Λ v p).hom := by
  rfl

attribute [local irreducible] CondensedRing.moduleObjectDerivedPullbackSquareComparison

private theorem total_forward_cube
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ p').hom.app
        ((CondensedRing.moduleObjectDerivedPullback Λ g).obj M) ≫
      (CondensedRing.upperStar Λ p').mapDerivedCategory.map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app M) ≫
      ((exactComp Λ p' g).symm ≪≫ eqToIso (congrArg
        (fun t : X' ⟶ Y ↦ (CondensedRing.upperStar Λ t).mapDerivedCategory) sq.w.symm) ≪≫
        exactComp Λ v p).hom.app M =
    (CondensedRing.moduleObjectDerivedPullbackSquareComparison Λ sq).hom.app M ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ v).hom.app
        ((CondensedRing.moduleObjectDerivedPullback Λ p).obj M) ≫
      (CondensedRing.upperStar Λ v).mapDerivedCategory.map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ p).hom.app M) := by
  have hr :
      (CondensedRing.leftDerivedUpperStarComp Λ v p).hom.app M ≫
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ v).hom.app
          ((CondensedRing.moduleObjectDerivedPullback Λ p).obj M) ≫
        (CondensedRing.upperStar Λ v).mapDerivedCategory.map
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ p).hom.app M) =
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (v ≫ p)).hom.app M ≫
        (exactComp Λ v p).hom.app M := by
    simpa only [exactComp_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      total_comp_normalization Λ v p M
  rw [totalSquare_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  exact paste_three _ _ _ _ _ _ _ _ _ _ _ _
    (total_inverse_comp Λ p' g M) (total_comparison_eq Λ sq.w.symm M) hr

private theorem inverse_functor_square
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    {G G' : C ⥤ A} {K K' : A ⥤ D} {F F' : C ⥤ B} {H H' : B ⥤ D}
    (qG : G ≅ G') (qK : K ≅ K') (qF : F ≅ F') (qH : H ≅ H')
    (α : G ⋙ K ⟶ F ⋙ H) (β : G' ⋙ K' ⟶ F' ⋙ H') (M : C)
    (h : qK.hom.app (G.obj M) ≫ K'.map (qG.hom.app M) ≫ β.app M =
      α.app M ≫ qH.hom.app (F.obj M) ≫ H'.map (qF.hom.app M)) :
    K'.map (qG.inv.app M) ≫ qK.inv.app (G.obj M) ≫ α.app M =
      β.app M ≫ H'.map (qF.inv.app M) ≫ qH.inv.app (F.obj M) := by
  have h' := invert_square (qK.app (G.obj M)) (K'.mapIso (qG.app M))
    (qH.app (F.obj M)) (H'.mapIso (qF.app M)) (α.app M) (β.app M)
    (by simpa only [Iso.app_hom, Functor.mapIso_hom] using h)
  simpa only [Iso.app_inv, Functor.mapIso_inv] using h'

private theorem identity_mate_cube
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F F' : A ⥤ B} {R : B ⥤ A} {G G' : A ⥤ C} {H H' : B ⥤ D}
    {K K' : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S) (a' : F' ⊣ R) (b' : K' ⊣ S)
    (pF : F ≅ F') (pG : G ≅ G') (pH : H ≅ H') (pK : K ≅ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ N : A,
      K'.map (pG.inv.app N) ≫ pK.inv.app (G.obj N) ≫ θ.app N =
        θ'.app N ≫ H'.map (pF.inv.app N) ≫ pH.inv.app (F.obj N))
    (hF : (mateEquiv a a' (TwoSquare.mk (𝟭 A) F F' (𝟭 B) pF.inv)) = 𝟙 R)
    (hK : (mateEquiv b b' (TwoSquare.mk (𝟭 C) K K' (𝟭 D) pK.inv)) = 𝟙 S)
    (E : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app E ≫ S.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ θ')).app E := by
  have h := exchangeMate_cube a b a' b' (𝟭 A) (𝟭 B) (𝟭 C) (𝟭 D)
    pF pG pH pK θ θ' (by simpa only [Functor.id_obj, Functor.id_map] using hc) E
  have h₁ := congr_app hF E
  have h₂ := congr_app hK (H.obj E)
  simp only [Functor.id_obj, Functor.id_map] at h h₁ h₂
  rw [h₁, h₂] at h
  simpa only [Functor.comp_obj, Functor.id_obj,
    NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.assoc, Category.id_comp, Category.comp_id] using h

private theorem identity_mate_forward_cube
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F F' : A ⥤ B} {R : B ⥤ A} {G G' : A ⥤ C} {H H' : B ⥤ D}
    {K K' : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S) (a' : F' ⊣ R) (b' : K' ⊣ S)
    (pF : F ≅ F') (pG : G ≅ G') (pH : H ≅ H') (pK : K ≅ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' θ'' : G' ⋙ K' ⟶ F' ⋙ H')
    (hθ : θ' = θ'')
    (hc : ∀ N : A,
      pK.hom.app (G.obj N) ≫ K'.map (pG.hom.app N) ≫ θ'.app N =
        θ.app N ≫ pH.hom.app (F.obj N) ≫ H'.map (pF.hom.app N))
    (hF : (mateEquiv a a' (TwoSquare.mk (𝟭 A) F F' (𝟭 B) pF.inv)) = 𝟙 R)
    (hK : (mateEquiv b b' (TwoSquare.mk (𝟭 C) K K' (𝟭 D) pK.inv)) = 𝟙 S)
    (E : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app E ≫ S.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ θ'')).app E := by
  subst θ''
  exact identity_mate_cube a b a' b' pF pG pH pK θ θ'
    (fun N ↦ inverse_functor_square pG pK pF pH θ θ' N (hc N)) hF hK E

private theorem arrow_of_mate_forward_cube
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F F' : A ⥤ B} {R : B ⥤ A} {G G' : A ⥤ C} {H H' : B ⥤ D}
    {K K' : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S) (a' : F' ⊣ R) (b' : K' ⊣ S)
    (pF : F ≅ F') (pG : G ≅ G') (pH : H ≅ H') (pK : K ≅ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' θ'' : G' ⋙ K' ⟶ F' ⋙ H')
    (hθ : θ' = θ'')
    (hc : ∀ N : A,
      pK.hom.app (G.obj N) ≫ K'.map (pG.hom.app N) ≫ θ'.app N =
        θ.app N ≫ pH.hom.app (F.obj N) ≫ H'.map (pF.hom.app N))
    (hF : (mateEquiv a a' (TwoSquare.mk (𝟭 A) F F' (𝟭 B) pF.inv)) = 𝟙 R)
    (hK : (mateEquiv b b' (TwoSquare.mk (𝟭 C) K K' (𝟭 D) pK.inv)) = 𝟙 S)
    (E : B)
    (τ : R ⋙ G ⟶ H ⋙ S) (τ' : R ⋙ G' ⟶ H' ⋙ S)
    (hτ : (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)) = τ)
    (hτ' : (mateEquiv a' b' (TwoSquare.mk _ _ _ _ θ'')) = τ') :
    Nonempty (Arrow.mk (τ.app E) ≅ Arrow.mk (τ'.app E)) := by
  have h := identity_mate_forward_cube a b a' b' pF pG pH pK θ θ' θ'' hθ hc hF hK E
  rw [hτ, hτ'] at h
  exact ⟨Arrow.isoMk (pG.app (R.obj E)) (S.mapIso (pH.app E)) (by
    simpa only [Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom,
      Arrow.mk_left, Arrow.mk_right, Functor.comp_obj] using h.symm)⟩

private theorem exactExchangeFor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    exactCondensedExchangeFor Λ sq =
  (mateEquiv
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso
        (condensedPullbackSquareFor Λ sq)).hom))
 := by
  delta exactCondensedExchangeFor
  rfl

private theorem totalExchangeFor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    CondensedRing.moduleObjectDerivedExchange Λ sq =
      (mateEquiv
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          Λ p)
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          Λ p')
        (TwoSquare.mk _ _ _ _ (CondensedRing.moduleObjectDerivedPullbackSquareComparison
          Λ sq).hom)) := by
  rfl

attribute [local irreducible] CondensedRing.moduleObjectDerivedExchange
/-- The canonical comparison from total left derived pullback to exact localization
identifies their specified exchange arrows.
Source: blueprint rational proper-base-change proof, exact derived factorization.
(blueprint: lem-sf-total-derived-exchange-exact-comparison).
Proof: the canonical comparison respects pullback compositors and equality transport.
Paste these identities across the commutative square. The total derived adjunction is
transported from the exact adjunction, so the right mate of each comparison is the
identity. Taking mates of the cube gives a commuting square with invertible vertical
maps, hence an isomorphism of exchange arrows. -/
theorem totalDerivedExchange_exact_comparisonFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Nonempty (Arrow.mk ((CondensedRing.moduleObjectDerivedExchange
      Λ sq).app M) ≅
        Arrow.mk ((exactCondensedExchangeFor Λ sq).app M)) := by
  exact arrow_of_mate_forward_cube
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ p)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ p')
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      Λ p').mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ p)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ v)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ p')
    (CondensedRing.moduleObjectDerivedPullbackSquareComparison
      Λ sq).hom
    (((exactComp Λ p' g).symm ≪≫
      eqToIso (congrArg (fun t : X' ⟶ Y ↦ (CondensedRing.upperStar
        Λ t).mapDerivedCategory) sq.w.symm) ≪≫
      exactComp Λ v p).hom)
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor Λ sq)).hom
    (exact_square_normalizationFor Λ sq)
    (fun N ↦ total_forward_cube Λ sq N)
    (total_mate_id Λ p)
    (total_mate_id Λ p') M
    (CondensedRing.moduleObjectDerivedExchange Λ sq)
    (exactCondensedExchangeFor Λ sq) (totalExchangeFor_eq Λ sq).symm (exactExchangeFor_eq Λ sq).symm

/-- At the canonical bundled coefficient the general exact exchange is the native
comparison's exact exchange. Source: the two specified compositor formulas.
(blueprint: lem-sf-total-derived-exchange-exact-comparison).
Proof: unfold the two ordinary square formulas; their compositors and adjunctions agree. -/
theorem exactCondensedExchangeFor_canonical (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    exactCondensedExchangeFor (Mon.mk (Profinite.padicAlgClRingObj l)).X sq =
      exactCondensedExchange l sq := by
  unfold exactCondensedExchangeFor exactCondensedExchange
    condensedPullbackSquareFor NativeEncoding.condensedPullbackSquare
  rfl

end AlgebraicGeometry.ProEtale
