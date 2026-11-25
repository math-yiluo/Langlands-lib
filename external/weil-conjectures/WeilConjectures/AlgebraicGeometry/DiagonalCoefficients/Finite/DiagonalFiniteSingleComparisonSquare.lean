/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteSingleComparison
public import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Coherence of cached single comparisons for inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
section
attribute [local instance 100000] CategoryTheory.sheafIsAbelian
attribute [local instance 100000] AlgebraicGeometry.Etale.ordinaryFiniteDerivedCategoryInstance
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem comp_iso_left_trans {C D E V : Type*}
    [Category C] [Category D] [Category E] [Category V]
    {S : C ⥤ D} {F G : D ⥤ V} {H : C ⥤ E} {I : E ⥤ V}
    (p : F ≅ G) (q : S ⋙ G ≅ H ⋙ I) (M : C) :
    (Functor.compIsoApp (Functor.isoWhiskerLeft S p ≪≫ q) M).hom =
      p.hom.app (S.obj M) ≫ (Functor.compIsoApp q M).hom := by
  unfold Functor.compIsoApp
  rfl

section SingleSquare

variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  [Abelian C] [Abelian D] [Abelian E] [Abelian V]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory V]
  (F : C ⥤ D) (G : D ⥤ V) (H : C ⥤ E) (I : E ⥤ V)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem single_square (e : F ⋙ G ≅ H ⋙ I) (M : C) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryCompIso H I).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      I.mapDerivedCategory.map ((Functor.compIsoApp (H.mapDerivedCategorySingleFunctor 0) M).hom) ≫
      (Functor.compIsoApp (I.mapDerivedCategorySingleFunctor 0) (H.obj M)).hom =
    G.mapDerivedCategory.map ((Functor.compIsoApp (F.mapDerivedCategorySingleFunctor 0) M).hom) ≫
      (Functor.compIsoApp (G.mapDerivedCategorySingleFunctor 0) (F.obj M)).hom ≫
      (DerivedCategory.singleFunctor V 0).map (e.hom.app M) := by
  simp only [Functor.compIsoApp, Iso.app_hom]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    ((DerivedCategory.singleFunctor C 0).obj M))).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G M)]

private theorem single_square_transport (e : F ⋙ G ≅ H ⋙ I) (M : C)
    {P : DerivedCategory D ⥤ DerivedCategory V}
    {Q : DerivedCategory C ⥤ DerivedCategory E}
    (p : P ≅ G.mapDerivedCategory) (q : Q ≅ H.mapDerivedCategory)
    {N : D} {T : E} {W : V} (c : F.obj M ≅ N) (d : I.obj T ≅ W)
    (t : H.obj M ⟶ T) (z : G.obj N ⟶ W)
    (ho : e.hom.app M ≫ I.map t ≫ d.hom = G.map c.hom ≫ z) :
    p.hom.app (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryCompIso H I).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      I.mapDerivedCategory.map (q.inv.app ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      I.mapDerivedCategory.map (q.hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        (Functor.compIsoApp (H.mapDerivedCategorySingleFunctor 0) M).hom ≫
        (DerivedCategory.singleFunctor E 0).map t) ≫
      (Functor.compIsoApp (I.mapDerivedCategorySingleFunctor 0) T).hom ≫
      (DerivedCategory.singleFunctor V 0).map d.hom =
    P.map ((Functor.compIsoApp (F.mapDerivedCategorySingleFunctor 0) M).hom ≫
        (DerivedCategory.singleFunctor D 0).map c.hom) ≫
      p.hom.app ((DerivedCategory.singleFunctor D 0).obj N) ≫
      (Functor.compIsoApp (G.mapDerivedCategorySingleFunctor 0) N).hom ≫
      (DerivedCategory.singleFunctor V 0).map z := by
  simp only [Functor.compIsoApp, Iso.app_hom]
  have hn := (I.mapDerivedCategorySingleFunctor 0).hom.naturality t
  have hg := (G.mapDerivedCategorySingleFunctor 0).hom.naturality c.hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hg
  simp only [Functor.map_comp, Category.assoc]
  rw [← I.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    I.mapDerivedCategory.map_id, Category.id_comp]
  have hs := single_square F G H I e M
  simp only [Functor.compIsoApp, Iso.app_hom] at hs
  erw [reassoc_of% hn, reassoc_of% hs]
  erw [p.hom.naturality_assoc, p.hom.naturality_assoc]
  erw [reassoc_of% hg]
  simp only [← Functor.map_comp]
  rw [ho]

private theorem single_square_transport_cached
    (SC : C ⥤ DerivedCategory C) (SE : E ⥤ DerivedCategory E)
    (cF : SC ⋙ F.mapDerivedCategory ≅ F ⋙ DerivedCategory.singleFunctor D 0)
    (cH : SC ⋙ H.mapDerivedCategory ≅ H ⋙ SE)
    (cI : SE ⋙ I.mapDerivedCategory ≅ I ⋙ DerivedCategory.singleFunctor V 0)
    (hSC : SC = DerivedCategory.singleFunctor C 0)
    (hSE : SE = DerivedCategory.singleFunctor E 0)
    (hF : HEq cF (F.mapDerivedCategorySingleFunctor 0))
    (hH : HEq cH (H.mapDerivedCategorySingleFunctor 0))
    (hI : HEq cI (I.mapDerivedCategorySingleFunctor 0))
    (e : F ⋙ G ≅ H ⋙ I) (M : C)
    {P : DerivedCategory D ⥤ DerivedCategory V}
    {Q : DerivedCategory C ⥤ DerivedCategory E}
    (p : P ≅ G.mapDerivedCategory) (q : Q ≅ H.mapDerivedCategory)
    {N : D} {T : E} {W : V} (c : F.obj M ≅ N) (d : I.obj T ≅ W)
    (t : H.obj M ⟶ T) (z : G.obj N ⟶ W)
    (ho : e.hom.app M ≫ I.map t ≫ d.hom = G.map c.hom ≫ z) :
    p.hom.app (F.mapDerivedCategory.obj (SC.obj M)) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app (SC.obj M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (SC.obj M) ≫
      (Functor.mapDerivedCategoryCompIso H I).inv.app (SC.obj M) ≫
      I.mapDerivedCategory.map (q.inv.app (SC.obj M)) ≫
      I.mapDerivedCategory.map
        ((Functor.compIsoApp (Functor.isoWhiskerLeft SC q ≪≫ cH) M).hom ≫ SE.map t) ≫
      (Functor.compIsoApp cI T).hom ≫ (DerivedCategory.singleFunctor V 0).map d.hom =
    P.map ((Functor.compIsoApp cF M).hom ≫
        (DerivedCategory.singleFunctor D 0).map c.hom) ≫
      p.hom.app ((DerivedCategory.singleFunctor D 0).obj N) ≫
      (Functor.compIsoApp (G.mapDerivedCategorySingleFunctor 0) N).hom ≫
      (DerivedCategory.singleFunctor V 0).map z := by
  subst SC
  subst SE
  cases eq_of_heq hF
  cases eq_of_heq hH
  cases eq_of_heq hI
  simpa only [comp_iso_left_trans, Category.assoc] using
    (single_square_transport F G H I e M p q c d t z ho)

end SingleSquare

/-- Exact-derived single comparisons carry an ordinary inverse-image comparison square
into the corresponding derived square, with the cached degree-zero embeddings.
Source: diagonal coefficient changes (1), compatibility of the finite comparison
with inverse image. (blueprint: lem-diagonal-finite-single-comparison-square).

Proof: compatibility of exact-derived comparisons with composition and natural
isomorphisms gives the undecorated square. Naturality moves the three ordinary
arrows across the single comparisons. Cancel the exact/left-derived comparison
isomorphisms and transport the single functors along their recorded equalities.
This applies to arbitrary sheaves and arrows; no nonempty or nonzero hypothesis
is used. -/
theorem finite_single_comparison_square (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    {N : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)}
    {T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {W : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)}
    (c : (comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj M ≅ N)
    (d : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj T ≅ W)
    (t : (Etale.upperStar (ModuleCat.{u + 1} A) f).obj M ⟶ T)
    (z : (upperStar (ModuleCat.{u + 1} A) f).obj N ⟶ W)
    (ho : (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app M ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map t ≫ d.hom =
      (upperStar (ModuleCat.{u + 1} A) f).map c.hom ≫ z) :
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
      ((Etale.ordinaryFiniteSingleFunctor A Y).obj M)) ≫
    (Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} A) Y) (upperStar
      (ModuleCat.{u + 1} A) f)).hom.app ((Etale.ordinaryFiniteSingleFunctor A Y).obj M) ≫
    (Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A)
      f)).hom.app ((Etale.ordinaryFiniteSingleFunctor A Y).obj M) ≫
    (Functor.mapDerivedCategoryCompIso (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)).inv.app ((Etale.ordinaryFiniteSingleFunctor A
      Y).obj M) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
      ((Etale.ordinaryFiniteSingleFunctor A Y).obj M)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
    ((Functor.compIsoApp (Functor.isoWhiskerLeft (Etale.ordinaryFiniteSingleFunctor A Y)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      (Etale.ordinaryFiniteSingleExactPullbackIso A f)) M).hom ≫ (Etale.ordinaryFiniteSingleFunctor
      A X).map t) ≫
    (Functor.compIsoApp (finiteSingleComparison A X) T).hom ≫ (DerivedCategory.singleFunctor (Sheaf
      (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map d.hom =
    (geoP1Pullback A f).map ((Functor.compIsoApp (finiteSingleComparison A Y) M).hom ≫
    (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).map
      c.hom) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
      ((DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
      N) ≫
    (Functor.compIsoApp ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0)
      N).hom ≫
    (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map z := by
  exact single_square_transport_cached
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y) (upperStar (ModuleCat.{u + 1} A) f)
    (Etale.upperStar (ModuleCat.{u + 1} A) f) (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (Etale.ordinaryFiniteSingleFunctor A Y) (Etale.ordinaryFiniteSingleFunctor A X)
    (finiteSingleComparison A Y) (Etale.ordinaryFiniteSingleExactPullbackIso A f)
    (finiteSingleComparison A X)
    (Etale.ordinaryFiniteSingleFunctor_eq A Y) (Etale.ordinaryFiniteSingleFunctor_eq A X)
    (finiteSingleComparison_heq A Y)
    (heq_of_eq (Etale.ordinaryFiniteSingleExactPullbackIso_eq A f))
    (finiteSingleComparison_heq A X)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)
    M
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    c d
    t z ho

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
end
