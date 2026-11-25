/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactSquareDerivedCounit
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
/-!
# Naturality of normalized right-derived squares

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-pur-derived-square-normalization-naturality).

A normalization by right-derived units determines a square on the derived category.
It therefore preserves ordinary naturality, horizontal composition, and commuting cubes.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactDerivedSquare
section
variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} Ap] [HasDerivedCategory.{w} Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [F.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
private def canonicalUnit (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ F.rightDerivedFunctor where
  app I := F.rightDerivedFunctorUnitQ I
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f
private theorem canonicalUnit_derived (F : A ⥤ B) [F.Additive] :
    F.rightDerivedFunctor.IsRightDerivedFunctor (canonicalUnit F)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  apply (derives F).isRightDerivedFunctor_of_isIso
  intro I
  have : I.obj.IsKInjective := I.property
  change IsIso (F.rightDerivedFunctorUnitQ I.obj)
  rw [F.rightDerivedFunctorUnitQ_eq]
  infer_instance
private theorem square_exists (c : F ⋙ y ≅ x ⋙ G)
    (hacyc : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
        x.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      ∀ M : CochainComplex A ℤ,
        y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
          b.hom.app (DerivedCategory.Q.obj M) ≫
          G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
        y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
          G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M) := by
  obtain ⟨b, hb, -⟩ := derivedCoefficientComparison F G x y
    x.mapDerivedCategory y.mapDerivedCategory
    x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors
    F.rightDerivedFunctor G.rightDerivedFunctor (canonicalUnit F) (canonicalUnit G)
    (fun I hI ↦ by
      have := hI
      change IsIso (F.rightDerivedFunctorUnitQ I)
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance) hacyc c
  refine ⟨b, ?_⟩
  intro M
  have h := congrArg (fun z ↦
    y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
      z ≫ G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M)) (hb M)
  simp only [canonicalUnit, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    ] at h
  erw [Functor.map_id] at h
  erw [Category.comp_id] at h
  exact h
private theorem square_unit_iso_iff (c : F ⋙ y ≅ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : ∀ M : CochainComplex A ℤ,
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
        b.hom.app (DerivedCategory.Q.obj M) ≫
        G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M))
    (M : CochainComplex A ℤ) :
    IsIso (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M)) ↔
      IsIso (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)) := by
  have : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M)) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app M)))
  have h := iff_of_eq (congrArg IsIso (hb M))
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h
private theorem acyclic_for_canonical
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (eta : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso A (.up ℤ))]
    (M : CochainComplex A ℤ) [IsIso (eta.app M)] :
    IsIso (F.rightDerivedFunctorUnitQ M) := by
  let := canonicalUnit_derived F
  let e := Functor.rightDerivedUnique RF F.rightDerivedFunctor eta (canonicalUnit F)
    (HomologicalComplex.quasiIso A (.up ℤ))
  have h : eta.app M ≫ e.hom.app (DerivedCategory.Q.obj M) =
      F.rightDerivedFunctorUnitQ M := by
    simpa only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Iso.refl, NatTrans.id_app, Category.id_comp, canonicalUnit] using
      Functor.rightDerivedNatTrans_app RF F.rightDerivedFunctor eta (canonicalUnit F)
        (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom M
  rw [← h]
  infer_instance
private theorem canonical_counit (L : B ⥤ A) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (I : CochainComplex A ℤ) :
    L.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := UnboundedExactTower.cochain_counit adj I
  simp only [UnboundedExactTower.cochainUnit, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv] at h
  erw [Functor.map_id] at h
  erw [Category.id_comp] at h
  exact h
private theorem square_unique (c : F ⋙ y ≅ x ⋙ G)
    (b b' : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : ∀ M : CochainComplex A ℤ,
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
        b.hom.app (DerivedCategory.Q.obj M) ≫
        G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M))
    (hb' : ∀ M : CochainComplex A ℤ,
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
        b'.hom.app (DerivedCategory.Q.obj M) ≫
        G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M) =
      y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)) : b = b' := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hI
  have : IsIso (F.rightDerivedFunctorUnitQ I) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have h : b.hom.app (DerivedCategory.Q.obj I) = b'.hom.app (DerivedCategory.Q.obj I) := by
    apply (cancel_epi (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I))).mp
    apply (cancel_mono
      (G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app I))).mp
    simpa only [Category.assoc] using (hb I).trans (hb' I).symm
  apply (cancel_mono ((x.mapDerivedCategory ⋙ G.rightDerivedFunctor).map e.hom)).mp
  rw [← b.hom.naturality e.hom, ← b'.hom.naturality e.hom, h]
private theorem coefficient_canonical_acyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R S : Sheaf K RingCat.{u}) (T : Sheaf L RingCat.{u})
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ (U : Cᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (hT : ∀ (U : Dᵒᵖ) (a b : T.obj.obj U), a * b = b * a)
    (a : R ⟶ S) (f : RingedToposMorphism R T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} T)]
    (I : CochainComplex (ringedSiteModules.{u} S) ℤ) [I.IsKInjective] :
    IsIso (f.modules.rightDerivedFunctorUnitQ
      (((SheafOfModules.restrictScalars.{u} a).mapHomologicalComplex (.up ℤ)).obj I)) := by
  obtain ⟨RF, eta, hRF, -, hI⟩ := coefficientAcyclicDerived R S T hR hS hT a f
  let := hRF
  have := hI I inferInstance
  exact acyclic_for_canonical f.modules RF eta _
private theorem cochain_hom_formula (L : B ⥤ A) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj M ⟶ I) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv
      (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
      (L.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
          F.rightDerivedFunctorUnitQ I := by
  apply (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [canonical_counit F L adj I]
  rw [reassoc_of% L.mapDerivedCategoryFactors_hom_naturality
    (((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I) f)]
  rw [← DerivedCategory.Q.map_comp]
  congr 2
  simpa only [Adjunction.homEquiv_counit] using
    (((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I).symm_apply_apply f).symm
omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap] in
private theorem squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r ≅ s ⋙ F) (K : CochainComplex Bp ℤ) :
    (Functor.mapDerivedCategorySquareIso hF).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex hF (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).inv.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem derived_unit_ext_general
    {E : Type (u + 1)} [Category.{u} E] [Abelian E] [HasDerivedCategory.{w} E]
    (Y : DerivedCategory.{w} B ⥤ DerivedCategory.{w} E)
    {T : DerivedCategory.{w} A ⥤ DerivedCategory.{w} E}
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
(blueprint: lem-pur-derived-square-normalization-naturality). -/
def unitNormalized
    (X : DerivedCategory.{w} A ⥤ DerivedCategory.{w} Ap)
    (Y : DerivedCategory.{w} B ⥤ DerivedCategory.{w} Bp)
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
(blueprint: lem-pur-derived-square-normalization-naturality).
Proof: evaluate on a K-injective representative, cancel the invertible source unit,
and use the two normalization equations. The ordinary square's naturality and the
naturality of the target derived unit then identify the two composites. Essential
surjectivity of K-injective representatives gives the equation on every object. -/
theorem normalized_naturality
    (x' : A ⥤ Ap) (y' : B ⥤ Bp) [x'.Additive] [y'.Additive]
    (X X' : DerivedCategory.{w} A ⥤ DerivedCategory.{w} Ap)
    (Y Y' : DerivedCategory.{w} B ⥤ DerivedCategory.{w} Bp)
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
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hcI :
      (NatTrans.mapHomologicalComplex d (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I =
      (NatTrans.mapHomologicalComplex c (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I) := by
    ext n
    exact hc (I.X n)
  rw [hcI, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rw [G.rightDerivedFunctorUnitQ_naturality]

private theorem normalized_comp
    {App Bpp : Type (u + 1)} [Category.{u} App] [Category.{u} Bpp]
    [Abelian App] [Abelian Bpp] [HasDerivedCategory.{w} App] [HasDerivedCategory.{w} Bpp]
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
  simp only [Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]
  erw [← reassoc_of% b'.hom.naturality (x.mapDerivedCategoryFactors.hom.app I)]
  simp only [Functor.comp_obj]
  erw [← y'.mapDerivedCategory.map_comp_assoc, ← y'.mapDerivedCategory.map_comp_assoc]
  erw [Category.assoc, hb I]
  simp only [Functor.map_comp, Category.assoc]
  erw [hb' ((x.mapHomologicalComplex (.up ℤ)).obj I)]
  erw [reassoc_of% (y'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I))]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem normalized_cube
    {App Bpp A2 B2 : Type (u + 1)}
    [Category.{u} App] [Category.{u} Bpp] [Category.{u} A2] [Category.{u} B2]
    [Abelian App] [Abelian Bpp] [Abelian A2] [Abelian B2]
    [HasDerivedCategory.{w} App] [HasDerivedCategory.{w} Bpp]
    [HasDerivedCategory.{w} A2] [HasDerivedCategory.{w} B2]
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
    (N : DerivedCategory.{w} A) :
    y'.mapDerivedCategory.map (b.hom.app N) ≫ b'.hom.app (x.mapDerivedCategory.obj N) ≫
        H.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso a).hom.app N) =
      (Functor.mapDerivedCategorySquareIso d).hom.app (F.rightDerivedFunctor.obj N) ≫
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
    a.hom d.hom (Functor.mapDerivedCategorySquareIso a).hom
    (Functor.mapDerivedCategorySquareIso d).hom
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
private theorem normalized_transition
    {Ak Bk : Type (u + 1)} [Category.{u} Ak] [Category.{u} Bk]
    [Abelian Ak] [Abelian Bk] [HasDerivedCategory.{w} Ak] [HasDerivedCategory.{w} Bk]
    [Abelian.HasKInjectiveResolutions Ak]
    (K : Ak ⥤ Bk) (xk : A ⥤ Ak) (yk : B ⥤ Bk) (tx : Ak ⥤ Ap) (ty : Bk ⥤ Bp)
    [K.Additive] [xk.Additive] [yk.Additive] [tx.Additive] [ty.Additive]
    [PreservesFiniteLimits xk] [PreservesFiniteColimits xk]
    [PreservesFiniteLimits yk] [PreservesFiniteColimits yk]
    [PreservesFiniteLimits tx] [PreservesFiniteColimits tx]
    [PreservesFiniteLimits ty] [PreservesFiniteColimits ty]
    (c : F ⋙ y ≅ x ⋙ G) (ck : F ⋙ yk ≅ xk ⋙ K) (ca : K ⋙ ty ≅ tx ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (bk : F.rightDerivedFunctor ⋙ yk.mapDerivedCategory ≅
      xk.mapDerivedCategory ⋙ K.rightDerivedFunctor)
    (ba : K.rightDerivedFunctor ⋙ ty.mapDerivedCategory ≅
      tx.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hbk : unitNormalized F K xk yk xk.mapDerivedCategory yk.mapDerivedCategory
      xk.mapDerivedCategoryFactors yk.mapDerivedCategoryFactors ck.hom bk.hom)
    (hba : unitNormalized K G tx ty tx.mapDerivedCategory ty.mapDerivedCategory
      tx.mapDerivedCategoryFactors ty.mapDerivedCategoryFactors ca.hom ba.hom)
    (a : x ⟶ xk ⋙ tx) (d : y ⟶ yk ⋙ ty)
    (ad : x.mapDerivedCategory ⟶ xk.mapDerivedCategory ⋙ tx.mapDerivedCategory)
    (dd : y.mapDerivedCategory ⟶ yk.mapDerivedCategory ⋙ ty.mapDerivedCategory)
    (ha : ∀ I : CochainComplex A ℤ,
      ad.app (DerivedCategory.Q.obj I) ≫ tx.mapDerivedCategory.map
          (xk.mapDerivedCategoryFactors.hom.app I) ≫
        tx.mapDerivedCategoryFactors.hom.app ((xk.mapHomologicalComplex (.up ℤ)).obj I) =
      x.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))
    (hd : ∀ I : CochainComplex B ℤ,
      dd.app (DerivedCategory.Q.obj I) ≫ ty.mapDerivedCategory.map
          (yk.mapDerivedCategoryFactors.hom.app I) ≫
        ty.mapDerivedCategoryFactors.hom.app ((yk.mapHomologicalComplex (.up ℤ)).obj I) =
      y.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d (.up ℤ)).app I))
    (hc : ∀ M : A, d.app (F.obj M) ≫ ty.map (ck.hom.app M) ≫ ca.hom.app (xk.obj M) =
      c.hom.app M ≫ G.map (a.app M))
    (N : DerivedCategory.{w} A) :
    dd.app (F.rightDerivedFunctor.obj N) ≫ ty.mapDerivedCategory.map (bk.hom.app N) ≫
        ba.hom.app (xk.mapDerivedCategory.obj N) =
      b.hom.app N ≫ G.rightDerivedFunctor.map (ad.app N) := by
  let xf := Functor.isoWhiskerRight xk.mapDerivedCategoryFactors tx.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (xk.mapHomologicalComplex (.up ℤ)) tx.mapDerivedCategoryFactors
  let yf := Functor.isoWhiskerRight yk.mapDerivedCategoryFactors ty.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (yk.mapHomologicalComplex (.up ℤ)) ty.mapDerivedCategoryFactors
  have h := normalized_naturality F G x y (xk ⋙ tx) (yk ⋙ ty)
    x.mapDerivedCategory (xk.mapDerivedCategory ⋙ tx.mapDerivedCategory)
    y.mapDerivedCategory (yk.mapDerivedCategory ⋙ ty.mapDerivedCategory)
    x.mapDerivedCategoryFactors xf y.mapDerivedCategoryFactors yf c.hom
    (Functor.whiskerRight ck.hom ty ≫ Functor.whiskerLeft xk ca.hom) b.hom
    (Functor.whiskerRight bk.hom ty.mapDerivedCategory ≫
      Functor.whiskerLeft xk.mapDerivedCategory ba.hom) hb
    (normalized_comp F K xk yk G tx ty ck ca bk ba hbk hba)
    a d ad dd
    (fun I ↦ by simpa only [xf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using ha I)
    (fun I ↦ by simpa only [yf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using hd I)
    (fun M ↦ by simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hc M)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg (fun q ↦ q.app N) h
end
end CategoryTheory.ExactDerivedSquare
