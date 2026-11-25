/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExchangeConstantIso
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # The derived pullback square on constant coefficients

Source: Stacks Project, Sites and Sheaves, Tag 0H7J; Derived Categories, Tag 015F
(blueprint: lem-pur-etale-sum-exchange-constants).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma sumSquareSingle
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (R : D ⥤ F) (L' : C ⥤ E) (R' : E ⥤ F)
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (τ : L ⋙ R ≅ L' ⋙ R') (M : C) :
    (Functor.mapDerivedCategorySquareIso τ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      R'.mapDerivedCategory.map ((L'.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (R'.mapDerivedCategorySingleFunctor 0).hom.app (L'.obj M) =
    R.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app (L.obj M) ≫
      (DerivedCategory.singleFunctor F 0).map (τ.hom.app M) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor L R M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private lemma sumSquareSingleMaps
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (R : D ⥤ F) (L' : C ⥤ E) (R' : E ⥤ F)
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (τ : L ⋙ R ≅ L' ⋙ R') (M : C) (N : D) (N' : E) (P : F)
    (c : L.obj M ⟶ N) (d : R.obj N ⟶ P)
    (c' : L'.obj M ⟶ N') (d' : R'.obj N' ⟶ P)
    (h : τ.hom.app M ≫ R'.map c' ≫ d' = R.map c ≫ d) :
    (Functor.mapDerivedCategorySquareIso τ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      R'.mapDerivedCategory.map ((L'.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor E 0).map c') ≫
      (R'.mapDerivedCategorySingleFunctor 0).hom.app N' ≫
      (DerivedCategory.singleFunctor F 0).map d' =
    R.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor D 0).map c) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor F 0).map d := by
  have hn := (R'.mapDerivedCategorySingleFunctor 0).hom.naturality c'
  have hn' := (R.mapDerivedCategorySingleFunctor 0).hom.naturality c
  simp only [Functor.comp_map] at hn hn'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hn']
  rw [reassoc_of% (sumSquareSingle L R L' R' τ M)]
  simp only [← Functor.map_comp, h]

private lemma sumSquareSingleIsos
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (R : D ⥤ F) (L' : C ⥤ E) (R' : E ⥤ F)
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (τ : L ⋙ R ≅ L' ⋙ R') (M : C) (N : D) (N' : E) (P : F)
    (c : L.obj M ≅ N) (d : R.obj N ≅ P)
    (c' : L'.obj M ≅ N') (d' : R'.obj N' ≅ P)
    (h : τ.hom.app M ≫ R'.map c'.hom ≫ d'.hom = R.map c.hom ≫ d.hom) :
    (Functor.mapDerivedCategorySquareIso τ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      R'.mapDerivedCategory.map
        (((L'.mapDerivedCategorySingleFunctor 0).app M ≪≫
          (DerivedCategory.singleFunctor E 0).mapIso c').hom) ≫
      ((R'.mapDerivedCategorySingleFunctor 0).app N' ≪≫
        (DerivedCategory.singleFunctor F 0).mapIso d').hom =
    R.mapDerivedCategory.map
        (((L.mapDerivedCategorySingleFunctor 0).app M ≪≫
          (DerivedCategory.singleFunctor D 0).mapIso c).hom) ≫
      ((R.mapDerivedCategorySingleFunctor 0).app N ≪≫
        (DerivedCategory.singleFunctor F 0).mapIso d).hom := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact sumSquareSingleMaps L R L' R' τ M N N' P c.hom d.hom c'.hom d'.hom h

/-- The canonical derived pullback square commutes with the specified constant comparisons.
Source: Stacks Project, Sites and Sheaves, Tag 0H7J; Derived Categories, Tag 015F
(blueprint: lem-pur-etale-sum-exchange-constants).

Proof: expand the sheaf pullback square into the two composition comparisons. Coherence of
`Scheme.upperStarConstantSheafIso_comp` identifies both routes with the constant comparison
for the common diagonal. Cancel the invertible diagonal comparison. The exact derived square
is compatible with the degree-zero embedding by the composition and natural-isomorphism
single-functor identities. Naturality on the four constant maps transports the sheaf equality
to the asserted derived equality. The private helpers carry out this transport in abstract
abelian categories before specializing to the four inverse-image functors. -/
theorem etaleSumExchangeConstantSquare
    (A : Type (u + 1)) [CommRing A]
    {U X X' : Scheme.{u}} (e : U ⟶ X) (w : X' ⟶ X) :
    (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback w e).toCommSq)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst w e)).mapDerivedCategory.map
        (etaleSumExchangeConstantIso A w).hom ≫
      (etaleSumExchangeConstantIso A (pullback.fst w e)).hom =
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory.map
        (etaleSumExchangeConstantIso A e).hom ≫
      (etaleSumExchangeConstantIso A (pullback.snd w e)).hom := by
  let B := ModuleCat.{u + 1} A
  let χ := squareUpperStarIso B (IsPullback.of_hasPullback w e).toCommSq
  let M := ModuleCat.of A A
  let C₀ := (constantSheaf X.smallEtaleTopology B).obj M
  have hc : χ.hom.app C₀ ≫
      (upperStar B (pullback.fst w e)).map
        ((Scheme.upperStarConstantSheafIso B w).hom.app M) ≫
      (Scheme.upperStarConstantSheafIso B (pullback.fst w e)).hom.app M =
    (upperStar B (pullback.snd w e)).map
        ((Scheme.upperStarConstantSheafIso B e).hom.app M) ≫
      (Scheme.upperStarConstantSheafIso B (pullback.snd w e)).hom.app M := by
    dsimp only [χ, squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [Category.assoc, Scheme.upperStarConstantSheafIso_comp]
    apply (cancel_epi ((upperStarComp B (pullback.snd w e) e
      (pullback.fst w e ≫ w) (pullback.condition (f := w) (g := e))).hom.app C₀)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    have hcomp (k : pullback w e ⟶ X) (hk : k = pullback.snd w e ≫ e) :
        (upperStarComp B (pullback.snd w e) e k hk).hom.app C₀ ≫
          (upperStar B (pullback.snd w e)).map
            ((Scheme.upperStarConstantSheafIso B e).hom.app M) ≫
          (Scheme.upperStarConstantSheafIso B (pullback.snd w e)).hom.app M =
        (Scheme.upperStarConstantSheafIso B k).hom.app M := by
      subst k
      exact Scheme.upperStarConstantSheafIso_comp B (pullback.snd w e) e M
    exact (hcomp _ (pullback.condition (f := w) (g := e))).symm
  exact sumSquareSingleIsos (upperStar B e) (upperStar B (pullback.snd w e))
    (upperStar B w) (upperStar B (pullback.fst w e)) χ C₀
    ((constantSheaf U.smallEtaleTopology B).obj M)
    ((constantSheaf X'.smallEtaleTopology B).obj M)
    ((constantSheaf (pullback w e).smallEtaleTopology B).obj M)
    ((Scheme.upperStarConstantSheafIso B e).app M)
    ((Scheme.upperStarConstantSheafIso B (pullback.snd w e)).app M)
    ((Scheme.upperStarConstantSheafIso B w).app M)
    ((Scheme.upperStarConstantSheafIso B (pullback.fst w e)).app M) hc

end AlgebraicGeometry.Etale
