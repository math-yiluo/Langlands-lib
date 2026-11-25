/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized derived cubes with independent localization universes

Source: Stacks, Cohomology on Sites, Tag 0D6E; the unit-normalization argument of
DerivedExactSquareCoherence, allowing each chosen derived category its own morphism universe.
(blueprint: lem-sf-independent-universe-derived-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

universe u wA wB wAp wBp wApp wBpp wA2 wB2 wE
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.IndependentDerivedCube
section LocalizedSquare
variable {A B C D : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} C] [Category.{u} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wAp} C] [HasDerivedCategory.{wBp} D]
  {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {J : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

/-- Localize an exact square, retaining a folded interface for its composition factors.
Source: exact localization and its canonical composition isomorphisms.
(blueprint: lem-sf-independent-universe-derived-cube). -/
@[irreducible] def localizedSquare (h : F ⋙ G ≅ H ⋙ J) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ J.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso h
end LocalizedSquare

section
variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wAp} Ap] [HasDerivedCategory.{wBp} Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [F.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap] in
private theorem squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r ≅ s ⋙ F) (K : CochainComplex Bp ℤ) :
    (localizedSquare hF).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex hF (.up ℤ)).hom.app K) := by
  rw [localizedSquare]
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

private theorem derived_unit_ext_general
    {E : Type (u + 1)} [Category.{u} E] [Abelian E] [HasDerivedCategory.{wE} E]
    (Y : DerivedCategory.{wB} B ⥤ DerivedCategory.{wE} E)
    {T : DerivedCategory.{wA} A ⥤ DerivedCategory.{wE} E}
    (a b : F.rightDerivedFunctor ⋙ Y ⟶ T)
    (h : ∀ M : CochainComplex A ℤ,
      Y.map (F.rightDerivedFunctorUnitQ M) ≫ a.app (DerivedCategory.Q.obj M) =
        Y.map (F.rightDerivedFunctorUnitQ M) ≫ b.app (DerivedCategory.Q.obj M)) : a = b := by
  apply NatTrans.ext
  funext N
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hI
  have : IsIso (F.rightDerivedFunctorUnitQ I) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hi : a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I) :=
    (cancel_epi (Y.map (F.rightDerivedFunctorUnitQ I))).mp (h I)
  apply (cancel_mono (T.map e.hom)).mp
  rw [← a.naturality e.hom, ← b.naturality e.hom, hi]

/-- A square normalized by the canonical right-derived units and localization factors.
Source: Stacks Tag 0D6E
(blueprint: lem-sf-independent-universe-derived-cube). -/
def unitNormalized
    (X : DerivedCategory.{wA} A ⥤ DerivedCategory.{wAp} Ap)
    (Y : DerivedCategory.{wB} B ⥤ DerivedCategory.{wBp} Bp)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F ⋙ y ⟶ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ Y ⟶ X ⋙ G.rightDerivedFunctor) : Prop :=
  ∀ I : CochainComplex A ℤ,
    Y.map (F.rightDerivedFunctorUnitQ I) ≫ b.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (xf.hom.app I) =
      yf.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I)
omit [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y] in
/-- A square normalized by right-derived units respects a morphism of ordinary squares.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E, uniqueness of right derivation.
(blueprint: lem-sf-independent-universe-derived-cube).
Proof: evaluate on a K-injective representative, cancel the invertible source unit,
and use the two normalization equations. The ordinary square's naturality and the
naturality of the target derived unit then identify the two composites. Essential
surjectivity of K-injective representatives gives the equation on every object. -/
private theorem normalized_naturality
    (x' : A ⥤ Ap) (y' : B ⥤ Bp) [x'.Additive] [y'.Additive]
    (X X' : DerivedCategory.{wA} A ⥤ DerivedCategory.{wAp} Ap)
    (Y Y' : DerivedCategory.{wB} B ⥤ DerivedCategory.{wBp} Bp)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (xf' : DerivedCategory.Q ⋙ X' ≅ x'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf' : DerivedCategory.Q ⋙ Y' ≅ y'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F ⋙ y ⟶ x ⋙ G) (c' : F ⋙ y' ⟶ x' ⋙ G)
    (b : F.rightDerivedFunctor ⋙ Y ⟶ X ⋙ G.rightDerivedFunctor)
    (b' : F.rightDerivedFunctor ⋙ Y' ⟶ X' ⋙ G.rightDerivedFunctor)
    (hn : unitNormalized F G x y X Y xf yf c b)
    (hn' : unitNormalized F G x' y' X' Y' xf' yf' c' b')
    (a : x ⟶ x') (d : y ⟶ y') (ad : X ⟶ X') (dd : Y ⟶ Y')
    (ha : ∀ I : CochainComplex A ℤ,
      ad.app (DerivedCategory.Q.obj I) ≫ xf'.hom.app I =
        xf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))
    (hd : ∀ I : CochainComplex B ℤ,
      dd.app (DerivedCategory.Q.obj I) ≫ yf'.hom.app I =
        yf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d (.up ℤ)).app I))
    (hc : ∀ M : A, d.app (F.obj M) ≫ c'.app M = c.app M ≫ G.map (a.app M)) :
    Functor.whiskerLeft F.rightDerivedFunctor dd ≫ b' =
      b ≫ Functor.whiskerRight ad G.rightDerivedFunctor := by
  apply derived_unit_ext_general F Y
  intro I
  apply (cancel_mono (G.rightDerivedFunctor.map (xf'.hom.app I))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [reassoc_of% dd.naturality (F.rightDerivedFunctorUnitQ I)]
  rw [hn' I]
  rw [reassoc_of% hd ((F.mapHomologicalComplex (.up ℤ)).obj I)]
  rw [← G.rightDerivedFunctor.map_comp, ha, Functor.map_comp]
  rw [reassoc_of% hn I]
  erw [← DerivedCategory.Q.map_comp_assoc]
  have hcI :
      (NatTrans.mapHomologicalComplex d (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I =
      (NatTrans.mapHomologicalComplex c (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I) := by
    ext n
    exact hc (I.X n)
  erw [hcI, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rw [G.rightDerivedFunctorUnitQ_naturality]

private theorem normalized_comp
    {App Bpp : Type (u + 1)} [Category.{u} App] [Category.{u} Bpp]
    [Abelian App] [Abelian Bpp] [HasDerivedCategory.{wApp} App] [HasDerivedCategory.{wBpp} Bpp]
    [Abelian.HasKInjectiveResolutions App]
    (H : App ⥤ Bpp) (x' : Ap ⥤ App) (y' : Bp ⥤ Bpp)
    [H.Additive] [x'.Additive] [y'.Additive]
    [PreservesFiniteLimits x'] [PreservesFiniteColimits x']
    [PreservesFiniteLimits y'] [PreservesFiniteColimits y']
    (c : F ⋙ y ≅ x ⋙ G) (c' : G ⋙ y' ≅ x' ⋙ H)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (b' : G.rightDerivedFunctor ⋙ y'.mapDerivedCategory ≅
      x'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hb' : unitNormalized G H x' y' x'.mapDerivedCategory y'.mapDerivedCategory
      x'.mapDerivedCategoryFactors y'.mapDerivedCategoryFactors c'.hom b'.hom) :
    unitNormalized F H (x ⋙ x') (y ⋙ y')
      (x.mapDerivedCategory ⋙ x'.mapDerivedCategory)
      (y.mapDerivedCategory ⋙ y'.mapDerivedCategory)
      (Functor.isoWhiskerRight x.mapDerivedCategoryFactors x'.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) x'.mapDerivedCategoryFactors)
      (Functor.isoWhiskerRight y.mapDerivedCategoryFactors y'.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (y.mapHomologicalComplex (.up ℤ)) y'.mapDerivedCategoryFactors)
      (Functor.whiskerRight c.hom y' ≫ Functor.whiskerLeft x c'.hom)
      (Functor.whiskerRight b.hom y'.mapDerivedCategory ≫
        Functor.whiskerLeft x.mapDerivedCategory b'.hom) := by
  intro I
  dsimp only [Functor.comp_map, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  simp only [Category.assoc, Functor.map_comp]
  erw [← reassoc_of% b'.hom.naturality (x.mapDerivedCategoryFactors.hom.app I)]
  erw [← y'.mapDerivedCategory.map_comp_assoc, ← y'.mapDerivedCategory.map_comp_assoc]
  erw [Category.assoc, hb I]
  simp only [Functor.map_comp, Category.assoc]
  erw [hb' ((x.mapHomologicalComplex (.up ℤ)).obj I)]
  erw [reassoc_of% (y'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I))]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  rfl

section CompositeSquares
variable {A B Ap Bp App Bpp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Category.{u} App] [Category.{u} Bpp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp] [Abelian App] [Abelian Bpp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wAp} Ap] [HasDerivedCategory.{wBp} Bp]
  [HasDerivedCategory.{wApp} App] [HasDerivedCategory.{wBpp} Bpp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  [Abelian.HasKInjectiveResolutions App]
  (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  (H : App ⥤ Bpp) (x' : Ap ⥤ App) (y' : Bp ⥤ Bpp)
  [F.Additive] [G.Additive] [H.Additive]
  [x.Additive] [y.Additive] [x'.Additive] [y'.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
  [PreservesFiniteLimits x'] [PreservesFiniteColimits x']
  [PreservesFiniteLimits y'] [PreservesFiniteColimits y']
  (c : F ⋙ y ≅ x ⋙ G) (c' : G ⋙ y' ≅ x' ⋙ H)
  (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
    x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
  (b' : G.rightDerivedFunctor ⋙ y'.mapDerivedCategory ≅
    x'.mapDerivedCategory ⋙ H.rightDerivedFunctor)

/-- Paste two ordinary comparison squares.
Source: Stacks Tag 0D6E, composition of squares.
(blueprint: lem-sf-independent-universe-derived-cube). -/
def compSquare : F ⋙ (y ⋙ y') ≅ (x ⋙ x') ⋙ H :=
  Functor.isoWhiskerRight c y' ≪≫ Functor.isoWhiskerLeft x c'

/-- Paste two derived squares and transport by the exact localization composition factors.
Source: Stacks Tag 0D6E, derived composition.
(blueprint: lem-sf-independent-universe-derived-cube). -/
private def compDerivedSquare :
    F.rightDerivedFunctor ⋙ (y ⋙ y').mapDerivedCategory ≅
      (x ⋙ x').mapDerivedCategory ⋙ H.rightDerivedFunctor :=
  Functor.isoWhiskerLeft F.rightDerivedFunctor (Functor.mapDerivedCategoryCompIso y y').symm ≪≫
    Functor.isoWhiskerRight b y'.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft x.mapDerivedCategory b' ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso x x')
          H.rightDerivedFunctor

private theorem compDerivedSquare_normalized
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hb' : unitNormalized G H x' y' x'.mapDerivedCategory y'.mapDerivedCategory
      x'.mapDerivedCategoryFactors y'.mapDerivedCategoryFactors c'.hom b'.hom) :
    unitNormalized F H (x ⋙ x') (y ⋙ y')
      (x ⋙ x').mapDerivedCategory (y ⋙ y').mapDerivedCategory
      (x ⋙ x').mapDerivedCategoryFactors (y ⋙ y').mapDerivedCategoryFactors
      (compSquare F G x y H x' y' c c').hom
      (compDerivedSquare F G x y H x' y' b b').hom := by
  intro I
  have hn := normalized_comp F G x y H x' y' c c' b b' hb hb' I
  dsimp only [compDerivedSquare, compSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← H.rightDerivedFunctor.map_comp]
  have hx := Functor.mapDerivedCategoryCompIso_hom_app_factors x x' I
  have hx' : (Functor.mapDerivedCategoryCompIso x x').hom.app (DerivedCategory.Q.obj I) ≫
      (x ⋙ x').mapDerivedCategoryFactors.hom.app I =
      x'.mapDerivedCategory.map (x.mapDerivedCategoryFactors.hom.app I) ≫
        x'.mapDerivedCategoryFactors.hom.app ((x.mapHomologicalComplex (.up ℤ)).obj I) := by
    calc
      _ = (Functor.mapDerivedCategoryCompIso x x').hom.app (DerivedCategory.Q.obj I) ≫
          ((Functor.mapDerivedCategoryCompIso x x').inv.app (DerivedCategory.Q.obj I) ≫
            x'.mapDerivedCategory.map (x.mapDerivedCategoryFactors.hom.app I) ≫
              x'.mapDerivedCategoryFactors.hom.app
                ((x.mapHomologicalComplex (.up ℤ)).obj I)) := congrArg _ hx.symm
      _ = _ := Iso.hom_inv_id_app_assoc _ _ _
  rw [hx']
  erw [H.rightDerivedFunctor.map_comp]
  rw [reassoc_of% (Functor.mapDerivedCategoryCompIso y y').inv.naturality
    (F.rightDerivedFunctorUnitQ I)]
  have hn' :
      y'.mapDerivedCategory.map (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I)) ≫
        y'.mapDerivedCategory.map (b.hom.app (DerivedCategory.Q.obj I)) ≫
          b'.hom.app (x.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
            H.rightDerivedFunctor.map
              (x'.mapDerivedCategory.map (x.mapDerivedCategoryFactors.hom.app I)) ≫
            H.rightDerivedFunctor.map
              (x'.mapDerivedCategoryFactors.hom.app
                ((x.mapHomologicalComplex (.up ℤ)).obj I)) =
      (y'.mapDerivedCategory.map
        (y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
          y'.mapDerivedCategoryFactors.hom.app
            ((y.mapHomologicalComplex (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj I))) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (compSquare F G x y H x' y' c c').hom
            (.up ℤ)).app I) ≫
          H.rightDerivedFunctorUnitQ (((x ⋙ x').mapHomologicalComplex (.up ℤ)).obj I) := by
    change y'.mapDerivedCategory.map (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I)) ≫
        (y'.mapDerivedCategory.map (b.hom.app (DerivedCategory.Q.obj I)) ≫
          b'.hom.app (x.mapDerivedCategory.obj (DerivedCategory.Q.obj I))) ≫
            H.rightDerivedFunctor.map
              (x'.mapDerivedCategory.map (x.mapDerivedCategoryFactors.hom.app I) ≫
                x'.mapDerivedCategoryFactors.hom.app
                  ((x.mapHomologicalComplex (.up ℤ)).obj I)) =
      (y'.mapDerivedCategory.map
        (y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
          y'.mapDerivedCategoryFactors.hom.app
            ((y.mapHomologicalComplex (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj I))) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (compSquare F G x y H x' y' c c').hom
            (.up ℤ)).app I) ≫
          H.rightDerivedFunctorUnitQ (((x ⋙ x').mapHomologicalComplex (.up ℤ)).obj I) at hn
    simpa only [Functor.map_comp, Category.assoc] using hn
  erw [hn']
  rw [← Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rfl
end CompositeSquares

/-- Right-derived unit normalization transports an ordinary cube with independently
chosen localization universes.

Source: Stacks, Cohomology on Sites, Tag 0D6E; the normalized cube argument.
(blueprint: lem-sf-independent-universe-derived-cube).

Proof: paste the two full-unit equations along each route. The ordinary cube is a
morphism of these pasted squares. Its exact-localization factors agree by the
composition factor equations. Evaluate the resulting naturality equation on a
K-injective representative, cancel its invertible right-derived unit, and transport
along the representative isomorphism to every derived object. All operations are
in the supplied derived categories; their morphism universes need not agree. -/
private theorem normalized_cube
    {App Bpp A2 B2 : Type (u + 1)}
    [Category.{u} App] [Category.{u} Bpp] [Category.{u} A2] [Category.{u} B2]
    [Abelian App] [Abelian Bpp] [Abelian A2] [Abelian B2]
    [HasDerivedCategory.{wApp} App] [HasDerivedCategory.{wBpp} Bpp]
    [HasDerivedCategory.{wA2} A2] [HasDerivedCategory.{wB2} B2]
    [Abelian.HasKInjectiveResolutions App] [Abelian.HasKInjectiveResolutions A2]
    (H : App ⥤ Bpp) (K : A2 ⥤ B2)
    (x' : Ap ⥤ App) (y' : Bp ⥤ Bpp)
    (z : A ⥤ A2) (t : B ⥤ B2) (z' : A2 ⥤ App) (t' : B2 ⥤ Bpp)
    [H.Additive] [K.Additive] [x'.Additive] [y'.Additive]
    [z.Additive] [t.Additive] [z'.Additive] [t'.Additive]
    [PreservesFiniteLimits x'] [PreservesFiniteColimits x']
    [PreservesFiniteLimits y'] [PreservesFiniteColimits y']
    [PreservesFiniteLimits z] [PreservesFiniteColimits z]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    [PreservesFiniteLimits z'] [PreservesFiniteColimits z']
    [PreservesFiniteLimits t'] [PreservesFiniteColimits t']
    (c : F ⋙ y ≅ x ⋙ G) (c' : G ⋙ y' ≅ x' ⋙ H)
    (cc : F ⋙ t ≅ z ⋙ K) (cc' : K ⋙ t' ≅ z' ⋙ H)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (b' : G.rightDerivedFunctor ⋙ y'.mapDerivedCategory ≅
      x'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (bb : F.rightDerivedFunctor ⋙ t.mapDerivedCategory ≅
      z.mapDerivedCategory ⋙ K.rightDerivedFunctor)
    (bb' : K.rightDerivedFunctor ⋙ t'.mapDerivedCategory ≅
      z'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hb' : unitNormalized G H x' y' x'.mapDerivedCategory y'.mapDerivedCategory
      x'.mapDerivedCategoryFactors y'.mapDerivedCategoryFactors c'.hom b'.hom)
    (hbb : unitNormalized F K z t z.mapDerivedCategory t.mapDerivedCategory
      z.mapDerivedCategoryFactors t.mapDerivedCategoryFactors cc.hom bb.hom)
    (hbb' : unitNormalized K H z' t' z'.mapDerivedCategory t'.mapDerivedCategory
      z'.mapDerivedCategoryFactors t'.mapDerivedCategoryFactors cc'.hom bb'.hom)
    (a : x ⋙ x' ≅ z ⋙ z') (d : y ⋙ y' ≅ t ⋙ t')
    (hc : ∀ M : A,
      d.hom.app (F.obj M) ≫ t'.map (cc.hom.app M) ≫ cc'.hom.app (z.obj M) =
        y'.map (c.hom.app M) ≫ c'.hom.app (x.obj M) ≫ H.map (a.hom.app M))
    (N : DerivedCategory.{wA} A) :
    y'.mapDerivedCategory.map (b.hom.app N) ≫ b'.hom.app (x.mapDerivedCategory.obj N) ≫
        H.rightDerivedFunctor.map ((localizedSquare a).hom.app N) =
      (localizedSquare d).hom.app (F.rightDerivedFunctor.obj N) ≫
        t'.mapDerivedCategory.map (bb.hom.app N) ≫ bb'.hom.app (z.mapDerivedCategory.obj N) := by
  let xf := Functor.isoWhiskerRight x.mapDerivedCategoryFactors x'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) x'.mapDerivedCategoryFactors
  let yf := Functor.isoWhiskerRight y.mapDerivedCategoryFactors y'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (y.mapHomologicalComplex (.up ℤ)) y'.mapDerivedCategoryFactors
  let zf := Functor.isoWhiskerRight z.mapDerivedCategoryFactors z'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (z.mapHomologicalComplex (.up ℤ)) z'.mapDerivedCategoryFactors
  let tf := Functor.isoWhiskerRight t.mapDerivedCategoryFactors t'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (t.mapHomologicalComplex (.up ℤ)) t'.mapDerivedCategoryFactors
  have h := normalized_naturality F H (x ⋙ x') (y ⋙ y') (z ⋙ z') (t ⋙ t')
    (x.mapDerivedCategory ⋙ x'.mapDerivedCategory)
    (z.mapDerivedCategory ⋙ z'.mapDerivedCategory)
    (y.mapDerivedCategory ⋙ y'.mapDerivedCategory)
    (t.mapDerivedCategory ⋙ t'.mapDerivedCategory) xf zf yf tf
    (Functor.whiskerRight c.hom y' ≫ Functor.whiskerLeft x c'.hom)
    (Functor.whiskerRight cc.hom t' ≫ Functor.whiskerLeft z cc'.hom)
    (Functor.whiskerRight b.hom y'.mapDerivedCategory ≫
      Functor.whiskerLeft x.mapDerivedCategory b'.hom)
    (Functor.whiskerRight bb.hom t'.mapDerivedCategory ≫
      Functor.whiskerLeft z.mapDerivedCategory bb'.hom)
    (normalized_comp F G x y H x' y' c c' b b' hb hb')
    (normalized_comp F K z t H z' t' cc cc' bb bb' hbb hbb')
    a.hom d.hom (localizedSquare a).hom
    (localizedSquare d).hom
    (fun I ↦ by simpa only [xf, zf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      NatIso.mapHomologicalComplex]
      using squareFactors x z' x' z a I)
    (fun I ↦ by simpa only [yf, tf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      NatIso.mapHomologicalComplex]
      using squareFactors y t' y' t d I)
    (fun M ↦ by simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hc M)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using (congrArg (fun q ↦ q.app N) h).symm

private theorem changeHorizontal
    {C0 C1 D0 D1 A0 A1 B0 B1 : Type*}
    [Category C0] [Category C1] [Category D0] [Category D1]
    [Category A0] [Category A1] [Category B0] [Category B1]
    (rU : A0 ⥤ A1) (rV : B0 ⥤ B1) (qS : A0 ⥤ B0) (qR : A1 ⥤ B1)
    (eU : C0 ⥤ A0) (eV : D0 ⥤ B0) (iU : C1 ⥤ A1) (iV : D1 ⥤ B1)
    (cU cU' : C0 ⥤ C1) (cV cV' : D0 ⥤ D1)
    (pC : C0 ⥤ D0) (pI : C1 ⥤ D1)
    (vU : cU ≅ cU') (vV : cV ≅ cV')
    (kU : cU' ⋙ iU ≅ eU ⋙ rU) (kV : cV' ⋙ iV ≅ eV ⋙ rV)
    (x : pI ⋙ iV ≅ iU ⋙ qR) (y : pC ⋙ eV ≅ eU ⋙ qS)
    (d : qS ⋙ rV ≅ rU ⋙ qR) (b : pC ⋙ cV ≅ cU ⋙ pI)
    (h : ∀ N : C0,
      kV.hom.app (pC.obj N) ≫ rV.map (y.hom.app N) ≫ d.hom.app (eU.obj N) =
        iV.map ((Functor.isoWhiskerLeft pC vV.symm ≪≫ b ≪≫
          Functor.isoWhiskerRight vU pI).hom.app N) ≫
            x.hom.app (cU'.obj N) ≫ qR.map (kU.hom.app N))
    (N : C0) :
    (Functor.isoWhiskerRight vV iV ≪≫ kV).hom.app (pC.obj N) ≫
        rV.map (y.hom.app N) ≫ d.hom.app (eU.obj N) =
      iV.map (b.hom.app N) ≫ x.hom.app (cU.obj N) ≫
        qR.map ((Functor.isoWhiskerRight vU iU ≪≫ kU).hom.app N) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [Category.assoc, h N]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← iV.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [iV.map_id, Category.id_comp]
  have hx := x.hom.naturality (vU.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hx
  rw [reassoc_of% hx]

end

section PastedCube
universe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9
variable {A0 A1 A2 B0 B1 B2 C0 C1 D0 D1 : Type (u + 1)}
  [Category.{u} A0] [Category.{u} A1] [Category.{u} A2]
  [Category.{u} B0] [Category.{u} B1] [Category.{u} B2]
  [Category.{u} C0] [Category.{u} C1] [Category.{u} D0] [Category.{u} D1]
  [Abelian A0] [Abelian A1] [Abelian A2]
  [Abelian B0] [Abelian B1] [Abelian B2]
  [Abelian C0] [Abelian C1] [Abelian D0] [Abelian D1]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w3} B0]
  [HasDerivedCategory.{w4} B1] [HasDerivedCategory.{w5} B2]
  [HasDerivedCategory.{w6} C0] [HasDerivedCategory.{w7} C1]
  [HasDerivedCategory.{w8} D0] [HasDerivedCategory.{w9} D1]
  [Abelian.HasKInjectiveResolutions A0] [Abelian.HasKInjectiveResolutions A1]
  [Abelian.HasKInjectiveResolutions A2] [Abelian.HasKInjectiveResolutions C0]
  [Abelian.HasKInjectiveResolutions C1]
  (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
  (G0 : C0 ⥤ D0) (G1 : C1 ⥤ D1)
  (sU : A0 ⥤ A1) (sV : B0 ⥤ B1) (tU : A1 ⥤ A2) (tV : B1 ⥤ B2)
  (iU : A2 ⥤ C1) (iV : B2 ⥤ D1) (eU : A0 ⥤ C0) (eV : B0 ⥤ D0)
  (rU : C0 ⥤ C1) (rV : D0 ⥤ D1)
  [F0.Additive] [F1.Additive] [F2.Additive] [G0.Additive] [G1.Additive]
  [sU.Additive] [sV.Additive] [tU.Additive] [tV.Additive]
  [iU.Additive] [iV.Additive] [eU.Additive] [eV.Additive] [rU.Additive] [rV.Additive]
  [PreservesFiniteLimits sU] [PreservesFiniteColimits sU]
  [PreservesFiniteLimits sV] [PreservesFiniteColimits sV]
  [PreservesFiniteLimits tU] [PreservesFiniteColimits tU]
  [PreservesFiniteLimits tV] [PreservesFiniteColimits tV]
  [PreservesFiniteLimits iU] [PreservesFiniteColimits iU]
  [PreservesFiniteLimits iV] [PreservesFiniteColimits iV]
  [PreservesFiniteLimits eU] [PreservesFiniteColimits eU]
  [PreservesFiniteLimits eV] [PreservesFiniteColimits eV]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
  (b0 : F0 ⋙ sV ≅ sU ⋙ F1) (b1 : F1 ⋙ tV ≅ tU ⋙ F2)
  (x : F2 ⋙ iV ≅ iU ⋙ G1) (y : F0 ⋙ eV ≅ eU ⋙ G0)
  (d : G0 ⋙ rV ≅ rU ⋙ G1)
  (B0d : F0.rightDerivedFunctor ⋙ sV.mapDerivedCategory ≅
    sU.mapDerivedCategory ⋙ F1.rightDerivedFunctor)
  (B1d : F1.rightDerivedFunctor ⋙ tV.mapDerivedCategory ≅
    tU.mapDerivedCategory ⋙ F2.rightDerivedFunctor)
  (X : F2.rightDerivedFunctor ⋙ iV.mapDerivedCategory ≅
    iU.mapDerivedCategory ⋙ G1.rightDerivedFunctor)
  (Y : F0.rightDerivedFunctor ⋙ eV.mapDerivedCategory ≅
    eU.mapDerivedCategory ⋙ G0.rightDerivedFunctor)
  (Dd : G0.rightDerivedFunctor ⋙ rV.mapDerivedCategory ≅
    rU.mapDerivedCategory ⋙ G1.rightDerivedFunctor)
  (hb0 : unitNormalized F0 F1 sU sV sU.mapDerivedCategory sV.mapDerivedCategory
    sU.mapDerivedCategoryFactors sV.mapDerivedCategoryFactors b0.hom B0d.hom)
  (hb1 : unitNormalized F1 F2 tU tV tU.mapDerivedCategory tV.mapDerivedCategory
    tU.mapDerivedCategoryFactors tV.mapDerivedCategoryFactors b1.hom B1d.hom)
  (hx : unitNormalized F2 G1 iU iV iU.mapDerivedCategory iV.mapDerivedCategory
    iU.mapDerivedCategoryFactors iV.mapDerivedCategoryFactors x.hom X.hom)
  (hy : unitNormalized F0 G0 eU eV eU.mapDerivedCategory eV.mapDerivedCategory
    eU.mapDerivedCategoryFactors eV.mapDerivedCategoryFactors y.hom Y.hom)
  (hd : unitNormalized G0 G1 rU rV rU.mapDerivedCategory rV.mapDerivedCategory
    rU.mapDerivedCategoryFactors rV.mapDerivedCategoryFactors d.hom Dd.hom)
  (kU : (sU ⋙ tU) ⋙ iU ≅ eU ⋙ rU) (kV : (sV ⋙ tV) ⋙ iV ≅ eV ⋙ rV)
  (h : ∀ M,
    kV.hom.app (F0.obj M) ≫ rV.map (y.hom.app M) ≫ d.hom.app (eU.obj M) =
      iV.map ((compSquare F0 F1 sU sV F2 tU tV b0 b1).hom.app M) ≫
        x.hom.app ((sU ⋙ tU).obj M) ≫ G1.map (kU.hom.app M))

include b0 b1 x y d hb0 hb1 hx hy hd h in
/-- The normalized cube for two successive exact restrictions, expressed using the
composite of their two specified localized functors.

Source: Stacks, Cohomology on Sites, Tag 0D6E; exact localization composition factors.
(blueprint: lem-sf-independent-universe-derived-cube).

Proof: apply normalized_cube to the ordinary composite restriction. Its derived
comparison is compDerivedSquare, normalized by the two full-unit equations. Conjugate
the horizontal functors by mapDerivedCategoryCompIso; naturality of X cancels the
composition factors. This gives the cube with the two specified derived restrictions. -/
theorem normalized_composite_cube :
    let KU := Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso sU tU)
      iU.mapDerivedCategory ≪≫ localizedSquare kU
    let KV := Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso sV tV)
      iV.mapDerivedCategory ≪≫ localizedSquare kV
    ∀ N,
      KV.hom.app (F0.rightDerivedFunctor.obj N) ≫
          rV.mapDerivedCategory.map (Y.hom.app N) ≫
          Dd.hom.app (eU.mapDerivedCategory.obj N) =
        iV.mapDerivedCategory.map
            ((Functor.isoWhiskerRight B0d tV.mapDerivedCategory ≪≫
              Functor.isoWhiskerLeft sU.mapDerivedCategory B1d).hom.app N) ≫
          X.hom.app ((sU.mapDerivedCategory ⋙ tU.mapDerivedCategory).obj N) ≫
          G1.rightDerivedFunctor.map (KU.hom.app N) := by
  dsimp only
  intro N
  have hb := compDerivedSquare_normalized F0 F1 sU sV F2 tU tV b0 b1 B0d B1d hb0 hb1
  have hOld (M) := (normalized_cube F0 F2 (sU ⋙ tU) (sV ⋙ tV) G1 G0
    iU iV eU eV rU rV (compSquare F0 F1 sU sV F2 tU tV b0 b1) x y d
    (compDerivedSquare F0 F1 sU sV F2 tU tV B0d B1d) X Y Dd hb hx hy hd kU kV h M).symm
  exact changeHorizontal rU.mapDerivedCategory rV.mapDerivedCategory G0.rightDerivedFunctor
    G1.rightDerivedFunctor eU.mapDerivedCategory eV.mapDerivedCategory
    iU.mapDerivedCategory iV.mapDerivedCategory
    (sU.mapDerivedCategory ⋙ tU.mapDerivedCategory) (sU ⋙ tU).mapDerivedCategory
    (sV.mapDerivedCategory ⋙ tV.mapDerivedCategory) (sV ⋙ tV).mapDerivedCategory
    F0.rightDerivedFunctor F2.rightDerivedFunctor
    (Functor.mapDerivedCategoryCompIso sU tU)
    (Functor.mapDerivedCategoryCompIso sV tV)
    (localizedSquare kU) (localizedSquare kV)
    X Y Dd (Functor.isoWhiskerRight B0d tV.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft sU.mapDerivedCategory B1d)
    (fun M ↦ by
      simpa only [compDerivedSquare, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using hOld M) N
end PastedCube

end CategoryTheory.IndependentDerivedCube
