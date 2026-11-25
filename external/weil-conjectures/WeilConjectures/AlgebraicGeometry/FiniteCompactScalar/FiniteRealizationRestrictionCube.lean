/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
public import WeilConjectures.CategoryTheory.Finite.FiniteRealizationMateAlgebra
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteRealizationOrdinaryRestrictionCube
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicDirectImageUnitNormalization

/-! # The restriction and direct-image cube for intrinsic realization

Source: Step 1 of lem-finite-realization-scalar-mate; Stacks Tags 0D6E, 0D6J and 07A6.
(blueprint: lem-finite-realization-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightDerivedFunctor AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] CategoryTheory.Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
open CategoryTheory.Limits

namespace MixedDerivedCube
section
variable {A B Ap Bp : Type*}
  [Category A] [Category B] [Category Ap] [Category Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory Ap] [HasDerivedCategory Bp]
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
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    (Y : DerivedCategory B ⥤ DerivedCategory E)
    {T : DerivedCategory A ⥤ DerivedCategory E}
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
private def unitNormalized
    (X : DerivedCategory A ⥤ DerivedCategory Ap)
    (Y : DerivedCategory B ⥤ DerivedCategory Bp)
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
private theorem normalized_naturality
    (x' : A ⥤ Ap) (y' : B ⥤ Bp) [x'.Additive] [y'.Additive]
    (X X' : DerivedCategory A ⥤ DerivedCategory Ap)
    (Y Y' : DerivedCategory B ⥤ DerivedCategory Bp)
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
    {App Bpp : Type*} [Category App] [Category Bpp]
    [Abelian App] [Abelian Bpp] [HasDerivedCategory App] [HasDerivedCategory Bpp]
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
    {App Bpp A2 B2 : Type*}
    [Category App] [Category Bpp] [Category A2] [Category B2]
    [Abelian App] [Abelian Bpp] [Abelian A2] [Abelian B2]
    [HasDerivedCategory App] [HasDerivedCategory Bpp]
    [HasDerivedCategory A2] [HasDerivedCategory B2]
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
    (N : DerivedCategory A) :
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

end
end MixedDerivedCube

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The inverse realization/restriction square, descended termwise.
Source: sfInverseRealizationRestriction, Step 1 of lem-finite-realization-scalar-mate.
(blueprint: lem-finite-realization-restriction-cube). -/
def realizationRestrictionRightIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    pbcDerivedRestrict (scalarRingMap φ T) ⋙
        (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence T B).inverse.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift := by
  let ρ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B := scalarRingMap φ T
  let e : pbcDerivedRestrict.{u} ρ ⋙
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence T B).inverse.mapDerivedCategory ⋙
      @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) := by
    simpa only [ρ, pbcDerivedRestrict, pbcRestrict, scalarRingMap, proEtaleConstantRingMap,
      proEtaleCoefficientRestrictScalars, sfFixedRestriction, Sheaf.restrictScalars,
      Sheaf.derivedRestrictScalars] using
      Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  exact e

/-- Its forward counterpart, using only the units and counits of realization.
Source: equivalence conjugation, Step 1 of lem-finite-realization-scalar-mate.
(blueprint: lem-finite-realization-restriction-cube). -/
def realizationRestrictionIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T B).functor ⋙
        pbcDerivedRestrict (scalarRingMap φ T) ≅
      Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  realizationRestrictionFromInverse (sfIntrinsicDerivedEquivalence T A)
    (sfIntrinsicDerivedEquivalence T B) (realizationRestrictionRightIso φ T)

private theorem forward_realization_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
        (sfIntrinsicModuleEquivalence T A).toAdjunction
        (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) =
      TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).inv := by
  apply NatTrans.ext
  funext M
  simp only [sfInverseRealizationRestriction, mateEquiv_apply,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp,
    Category.assoc]
  dsimp only [Equivalence.symm, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.counit, TwoSquare.mk, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  all_goals rfl

private theorem realization_functor (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).functor =
      (sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory := rfl

private theorem realization_inverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).inverse =
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory := rfl

private theorem realization_adjunction (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).toAdjunction =
      (sfIntrinsicModuleEquivalence T A).toAdjunction.mapDerivedCategoryAdjunction := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro H
  rw [Adjunction.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
  change ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
    (Functor.mapDerivedCategoryNatIso (sfIntrinsicModuleEquivalence T A).counitIso).hom ≫
      (Functor.mapDerivedCategoryIdIso _).hom).app (DerivedCategory.Qh.obj H) = _
  simp only [NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 2
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  congr 1

private theorem inverse_realization_unit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (sfFixedRestriction T φ).map ((sfIntrinsicModuleEquivalence T B).unitIso.hom.app M) ≫
        (sfInverseRealizationRestriction T φ).inv.app
          ((sfIntrinsicModuleEquivalence T B).functor.obj M) =
      (sfIntrinsicModuleEquivalence T A).unitIso.hom.app
          ((sfFixedRestriction T φ).obj M) ≫
        (sfIntrinsicModuleEquivalence T A).inverse.map
          ((sfRealizationRestriction T φ).inv.app M) := by
  have h := unit_mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
    (sfIntrinsicModuleEquivalence T A).toAdjunction
    (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) M
  rw [forward_realization_mate] at h
  exact h

private theorem square_symm_hom
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso q.symm).hom =
      (Functor.mapDerivedCategorySquareIso q).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem conjugate_eq_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (EA : A ≌ C) (EB : B ≌ D) (U : D ⥤ C) (V : B ⥤ A)
    (q : U ⋙ EA.inverse ≅ EB.inverse ⋙ V)
    (r : EB.functor ⋙ U ≅ V ⋙ EA.functor)
    (h : ∀ M, V.map (EB.unitIso.hom.app M) ≫ q.inv.app (EB.functor.obj M) =
      EA.unitIso.hom.app (V.obj M) ≫ EA.inverse.map (r.inv.app M)) :
    realizationRestrictionFromInverse EA EB q = r := by
  have hp (M) : q.hom.app (EB.functor.obj M) ≫ V.map (EB.unitIso.inv.app M) =
      EA.inverse.map (r.hom.app M) ≫ EA.unitIso.inv.app (V.obj M) := by
    have hh : V.mapIso (EB.unitIso.app M) ≪≫ (q.app (EB.functor.obj M)).symm =
        EA.unitIso.app (V.obj M) ≪≫ (EA.inverse.mapIso (r.app M)).symm := Iso.ext (h M)
    exact congrArg Iso.inv hh
  apply Iso.ext
  ext M
  change EA.counitIso.inv.app _ ≫ EA.functor.map (q.hom.app (EB.functor.obj M)) ≫
    EA.functor.map (V.map (EB.unitIso.inv.app M)) = r.hom.app M
  rw [← EA.functor.map_comp, hp, EA.functor.map_comp]
  have hn := EA.counitIso.inv.naturality (r.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← reassoc_of% hn, ← EA.counit_app_functor]
  simp only [Equivalence.counit, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

private theorem restriction_eq
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    realizationRestrictionIso φ T =
      Functor.mapDerivedCategorySquareIso (sfRealizationRestriction T φ) := by
  let EA := sfIntrinsicDerivedEquivalence T A
  let EB := sfIntrinsicDerivedEquivalence T B
  let a : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B :=
    RingHom.ulift.{u + 1, u + 1, u, u} φ
  let V := Sheaf.derivedRestrictScalars (ProEt.topology T) a
  let q := Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  let r := Functor.mapDerivedCategorySquareIso (sfRealizationRestriction T φ)
  have hq (M) : V.map (EB.unitIso.hom.app M) ≫ q.inv.app (EB.functor.obj M) =
      EA.unitIso.hom.app (V.obj M) ≫ EA.inverse.map (r.inv.app M) := by
    have hM := Adjunction.mapDerivedCategoryAdjunction_mate
      (sfIntrinsicModuleEquivalence T B).toAdjunction
      (sfIntrinsicModuleEquivalence T A).toAdjunction
      (sfInverseRealizationRestriction T φ).symm
      (sfRealizationRestriction T φ).symm
      (fun N ↦ (inverse_realization_unit T φ N).symm) M
    rw [← realization_adjunction T A, ← realization_adjunction T B] at hM
    simpa only [square_symm_hom, EA, EB, q, r, V, a,
      sfFixedRestriction, Sheaf.derivedRestrictScalars, Sheaf.restrictScalars,
      realization_functor, realization_inverse, Equivalence.toAdjunction_unit,
      Equivalence.unit, Functor.comp_obj, Functor.id_obj] using hM.symm
  exact conjugate_eq_of_unit EA EB (proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory
    V q r hq

/-- The realization/restriction square commutes with the specified direct-image squares.

Source: Stacks Tags 0D6E, 0D6J and 07A6; Step 1 of
`lem-finite-realization-scalar-mate`.
(blueprint: lem-finite-realization-restriction-cube).

Proof: identify the conjugated restriction square with the exact localization of
sfRealizationRestriction using the derived mate equation and realization triangles.
On ordinary sheaves, the scalar comparisons are identities on sections; evaluating
on the scalar-unit sections proves the cube, since those unit maps are invertible.
The K-injective normalization of each realization comparison gives its inverse's
right-derived unit equation. Naturality along a K-injective resolution extends this
equation to every complex. The intrinsic restriction comparison and fixed-scalar
restriction mate already satisfy the corresponding all-complex unit equations.
Apply the proved normalized derived cube to these four equations and the ordinary
cube. Cancel its inverse comparison isomorphisms to recover the forward equation.
No restriction functor is asserted to preserve K-injectivity. -/
theorem realizationRestriction_directImage_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (L : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    (proEtaleConstantDerivedDirectImage g A).map
        ((realizationRestrictionIso φ Z).hom.app L) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology Z) φ.ulift).obj L) ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((ProEtale.fixedScalarRestrictionDirectImage φ.ulift g).hom.app L) =
    (sfDerivedImageRestriction g φ).hom.app
        ((sfIntrinsicDerivedEquivalence Z B).functor.obj L) ≫
      (pbcDerivedRestrict (scalarRingMap φ Y)).map
        ((sfIntrinsicDerivedDirectImageComparison g B).hom.app L) ≫
      (realizationRestrictionIso φ Y).hom.app
        ((ProEtale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor.obj L)  := by
  let QB := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g
  let QA := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g
  let PB := proEtaleConstantModuleDirectImage g B
  let PA := proEtaleConstantModuleDirectImage g A
  let EZB := (sfIntrinsicModuleEquivalence Z B).functor
  let EYB := (sfIntrinsicModuleEquivalence Y B).functor
  let EZA := (sfIntrinsicModuleEquivalence Z A).functor
  let EYA := (sfIntrinsicModuleEquivalence Y A).functor
  let UZ := proEtaleCoefficientRestrictScalars Z φ
  let UY := proEtaleCoefficientRestrictScalars Y φ
  let VZ := sfFixedRestriction Z φ
  let VY := sfFixedRestriction Y φ
  let cZ := sfRealizationRestriction Z φ
  let cY := sfRealizationRestriction Y φ
  let dA := sfIntrinsicDirectImageComparison g A
  let dB := sfIntrinsicDirectImageComparison g B
  let h := proEtaleCoefficientDirectImageComparison g φ
  let t := ProEtale.fixedScalarRestrictionDirectImageUnderived
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) g
  have ho (M) : cY.hom.app (QB.obj M) ≫ EYA.map (t.hom.app M) ≫
      dA.inv.app (VZ.obj M) = UY.map (dB.inv.app M) ≫
        h.hom.app (EZB.obj M) ≫ PA.map (cZ.hom.app M) := by
    apply (cancel_epi (UY.map (dB.hom.app M))).mp
    apply (cancel_epi (h.inv.app (EZB.obj M))).mp
    apply (cancel_mono (dA.hom.app (VZ.obj M))).mp
    simp only [Category.assoc, ← UY.map_comp_assoc, Iso.hom_inv_id_app,
      UY.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rw [show t = Iso.refl _ from
      ProEtale.fixedScalarRestrictionDirectImageUnderived_eq
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) g]
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj]
    have hh := realizationRestriction_ordinary_directImage_cube φ g M
    rw [EYA.map_id]
    apply (cancel_epi (h.hom.app (EZB.obj M))).mp
    simpa only [Category.assoc, h, UY, dB, cY, QB, PA, cZ, dA, EZB, VZ, EYA,
      Functor.map_id, Category.id_comp, Category.comp_id,
      Iso.hom_inv_id_app_assoc] using
      congrArg (fun z ↦ h.hom.app (EZB.obj M) ≫ z) hh.symm
  have hc := MixedDerivedCube.normalized_cube QB PB EZB EYB PA QA UZ UY VZ VY EZA EYA
    dB.symm h t dA.symm
    (sfIntrinsicDerivedDirectImageComparison g B).symm
    (sfDerivedImageRestriction g φ).symm
    (ProEtale.fixedScalarRestrictionDirectImage φ.ulift g).symm
    (sfIntrinsicDerivedDirectImageComparison g A).symm
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors B g)
    (WeilConjectures.compactSupportScalarDirectNormalization g φ)
    (ProEtale.fixedScalarRestrictionDirectImage_unitQ_factors
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) g)
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A g)
    cZ cY ho L
  simp only [Iso.symm_hom] at hc
  rw [restriction_eq, restriction_eq]
  change PA.rightDerivedFunctor.map
      ((Functor.mapDerivedCategorySquareIso cZ).hom.app L) ≫
    (sfIntrinsicDerivedDirectImageComparison g A).hom.app (VZ.mapDerivedCategory.obj L) ≫
    EYA.mapDerivedCategory.map
      ((ProEtale.fixedScalarRestrictionDirectImage
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) g).hom.app L) =
    (sfDerivedImageRestriction g φ).hom.app (EZB.mapDerivedCategory.obj L) ≫
    UY.mapDerivedCategory.map ((sfIntrinsicDerivedDirectImageComparison g B).hom.app L) ≫
    (Functor.mapDerivedCategorySquareIso cY).hom.app (QB.rightDerivedFunctor.obj L)
  apply (cancel_epi
    (UY.mapDerivedCategory.map ((sfIntrinsicDerivedDirectImageComparison g B).inv.app L) ≫
      (sfDerivedImageRestriction g φ).inv.app (EZB.mapDerivedCategory.obj L))).mp
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  simp only [← EYA.mapDerivedCategory.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj,
    ← UY.mapDerivedCategory.map_comp_assoc]
  erw [EYA.mapDerivedCategory.map_id, UY.mapDerivedCategory.map_id]
  erw [Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Scheme.FiniteCompactScalar
