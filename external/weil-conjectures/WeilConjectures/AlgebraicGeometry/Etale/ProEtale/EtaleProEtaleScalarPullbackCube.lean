/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The etale/pro-etale scalar and inverse-image cube

Source: Stacks Project, Cohomology on Sites, Tag 0D6D,
`lemma-derived-pullback-composition`, with Tags 06YS, 0G7E, 06YY and 07A4;
Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private abbrev adjLeft {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (_a : L ⊣ R) := L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStar (ModuleCat.{u + 1} A) f).map ((pbcComparisonRestrict Y a).inv.app N) ≫
      (upperStarRestrictScalarsIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) a).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f).hom.app N) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.upperStarRestrictScalarsIsoSheaf a f).hom.app N) ≫
      (pbcComparisonRestrict X a).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) f).obj N) := by
  let cyA := comparisonAdjunction (ModuleCat.{u + 1} A) Y
  let cxA := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let cyB := comparisonAdjunction (ModuleCat.{u + 1} B) Y
  let cxB := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let pA := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let pB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let lA := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let lB := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let ey := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology a
  let ex := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology a
  let py := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a
  let px := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a
  let e₁ := Functor.isoWhiskerRight (pbcComparisonRestrict Y a).symm (adjLeft pA)
  let e₂ := Functor.associator (adjLeft cyB) (adjLeft py) (adjLeft pA)
  let e₃ := Functor.isoWhiskerLeft (adjLeft cyB) (upperStarRestrictScalarsIso a f)
  let e₄ := (Functor.associator (adjLeft cyB) (adjLeft pB) (adjLeft px)).symm
  let e₅ := Functor.isoWhiskerRight
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f) (adjLeft px)
  let e₁' := Functor.associator (adjLeft ey) (adjLeft cyA) (adjLeft pA)
  let e₂' := Functor.isoWhiskerLeft (adjLeft ey)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)
  let e₃' := (Functor.associator (adjLeft ey) (adjLeft lA) (adjLeft cxA)).symm
  let e₄' := Functor.isoWhiskerRight (Etale.upperStarRestrictScalarsIsoSheaf a f) (adjLeft cxA)
  let e₅' := Functor.associator (adjLeft lB) (adjLeft ex) (adjLeft cxA)
  let e₆' := Functor.isoWhiskerLeft (adjLeft lB) (pbcComparisonRestrict X a).symm
  let e₇' := (Functor.associator (adjLeft lB) (adjLeft cxB) (adjLeft px)).symm
  have h : (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e₄) ≪≫ e₅ =
      (((((e₁' ≪≫ e₂') ≪≫ e₃') ≪≫ e₄') ≪≫ e₅') ≪≫ e₆') ≪≫ e₇' := by
    apply (conjugateIsoEquiv ((lB.comp cxB).comp px) ((ey.comp cyA).comp pA)).injective
    rw [conjugateIsoEquiv_trans _ ((cyB.comp pB).comp px),
      conjugateIsoEquiv_trans _ (cyB.comp (pB.comp px)),
      conjugateIsoEquiv_trans _ (cyB.comp (py.comp pA)),
      conjugateIsoEquiv_trans _ ((cyB.comp py).comp pA)]
    rw [conjugateIsoEquiv_trans _ (lB.comp (cxB.comp px)),
      conjugateIsoEquiv_trans _ (lB.comp (ex.comp cxA)),
      conjugateIsoEquiv_trans _ ((lB.comp ex).comp cxA),
      conjugateIsoEquiv_trans _ ((ey.comp lA).comp cxA),
      conjugateIsoEquiv_trans _ (ey.comp (lA.comp cxA)),
      conjugateIsoEquiv_trans _ (ey.comp (cyA.comp pA))]
    dsimp only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇']
    simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_isoWhiskerLeft]
    simp only [cyA, cxA, cyB, cxB, pA, pB, lA, lB, ey, ex, py, px,
      pbcComparisonRestrict, comparisonUpperStarCompUpperStarIso,
      upperStarRestrictScalarsIso, Etale.upperStarRestrictScalarsIsoSheaf,
      Adjunction.leftAdjointUniq, conjugateIsoEquiv_iso_symm,
      Equiv.apply_symm_apply, conjugateIsoEquiv_associator]
    erw [Equiv.apply_symm_apply]
    ext F V x
    simp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp
    rfl
  simpa only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, pA, px, cyB, ey, cxA, lB] using
    congrArg (fun e ↦ e.hom.app N) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict Y a).inv.app N) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a).map
        ((Functor.mapDerivedCategorySquareIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f)).hom.app N) =
    (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)).hom.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom.app N) ≫
      (pbcDerivedComparisonRestrict X a).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj N) := by
  let r₀ := Sheaf.restrictScalars Y.smallEtaleTopology a
  let r₁ := Sheaf.restrictScalars (Scheme.ProEt.topology Y) a
  let r₂ := Sheaf.restrictScalars (Scheme.ProEt.topology X) a
  let cA := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let cB := comparisonUpperStar (ModuleCat.{u + 1} B) Y
  let pA := upperStar (ModuleCat.{u + 1} A) f
  let pB := upperStar (ModuleCat.{u + 1} B) f
  let dA := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f
  let dB := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f
  let α : r₀ ⋙ (cA ⋙ pA) ≅ (cB ⋙ pB) ⋙ r₂ :=
    (Functor.associator r₀ cA pA).symm ≪≫
      Functor.isoWhiskerRight (pbcComparisonRestrict Y a).symm pA ≪≫
      Functor.associator cB r₁ pA ≪≫
      Functor.isoWhiskerLeft cB (upperStarRestrictScalarsIso a f) ≪≫
      (Functor.associator cB pB r₂).symm
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (pbcComparisonRestrict Y a).symm (upperStarRestrictScalarsIso a f) α
    (Iso.refl (cA ⋙ pA)) (Iso.refl (cB ⋙ pB)) (fun K ↦ by
      simp only [α, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      dsimp only [cA, cB, pA, pB, r₀, r₁, r₂, Functor.comp_obj]
      simp) N
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (Etale.upperStarRestrictScalarsIsoSheaf a f) (pbcComparisonRestrict X a).symm α
    dA dB (fun K ↦ by
      simpa only [α, cA, cB, pA, pB, r₀, r₁, r₂, dA, dB,
        Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using
        ordinary_restriction_cube a f K) N
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp] at h₁
  have htdA : (Functor.mapDerivedCategoryTriangleIso dA).hom =
      (Functor.mapDerivedCategoryCompIso cA pA).inv ≫
        (Functor.mapDerivedCategorySquareIso dA).hom := by
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso]
  have htdB : (Functor.mapDerivedCategoryTriangleIso dB).hom =
      (Functor.mapDerivedCategoryCompIso cB pB).inv ≫
        (Functor.mapDerivedCategorySquareIso dB).hom := by
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso]
  erw [htdA, htdB] at h₂
  simp only [NatTrans.comp_app, Functor.map_comp, ← Category.assoc] at h₂
  erw [h₁] at h₂
  have h := (cancel_epi ((Functor.mapDerivedCategoryCompIso cA pA).inv.app
    (r₀.mapDerivedCategory.obj N))).1
      (by simpa only [Category.assoc, Iso.symm_hom, cA, pA, r₀] using h₂)
  simpa only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    pbcDerivedComparisonRestrict, Iso.symm_inv, Sheaf.derivedRestrictScalars,
    Category.assoc, cA, pA, cB, pB, dA, dB, r₀, r₂] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    L(upperStar (ModuleCat.{u + 1} A) f).map
        ((pbcDerivedComparisonRestrict Y a).inv.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso B f).hom.app N) =
    (directImageComparisonAmbientPullbackIso A f).hom.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.scalarRestrictionPullbackIso a f).hom.app N) ≫
      (pbcDerivedComparisonRestrict X a).inv.app
        (L(Etale.upperStar (ModuleCat.{u + 1} B) f).obj N) := by
  unfold leftDerivedUpperStarRestrictScalarsIso directImageComparisonAmbientPullbackIso
    Etale.scalarRestrictionPullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.naturality_assoc]
  erw [(pbcDerivedComparisonRestrict X a).inv.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  have h := exact_restriction_cube a f N
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] at h
  erw [reassoc_of% h]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_whiskerTop
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reverse_scalar_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (scalarPullbackReverseProEtale a f).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫
      L(upperStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction Y a).hom.app M) ≫
      (directImageComparisonAmbientPullbackIso B f).hom.app
        ((pbcFixedScalarExtension Y.smallEtaleTopology a).obj M) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso A f).hom.app M) ≫
      (pbcComparisonReduction X a).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((scalarPullbackReverseEtale a f).app M) := by
  let a₀ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  let a₁ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) a)
  let a₁' := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)
  let a₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a)
  let sy := (mateEquiv a₀ a₁).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict Y a).inv)
  let sp := (mateEquiv a₁ a₂).symm
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)
  let se := (mateEquiv a₀ a₁').symm
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)
  let sx := (mateEquiv a₁' a₂).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict X a).inv)
  have h : (TwoSquare.hComp sy sp).whiskerBottom
        (directImageComparisonAmbientPullbackIso B f).hom =
      (TwoSquare.hComp se sx).whiskerTop (directImageComparisonAmbientPullbackIso A f).hom := by
    apply (mateEquiv a₀ a₂).injective
    rw [mateEquiv_whiskerBottom, mate_whiskerTop,
      mateEquiv_vcomp a₀ a₁ a₂, mateEquiv_vcomp a₀ a₁' a₂]
    dsimp only [sy, sp, se, sx]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext N
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using derived_restriction_cube a f N
  simpa only [sy, sp, se, sx, a₀, a₁, a₁', a₂,
    TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    pbcComparisonReduction, asIso_hom, pbcComparisonReductionMap, pbcFixedScalarExtension,
    scalarPullbackReverseProEtale, scalarPullbackReverseEtale,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun t ↦ t.app M) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical inverse-image square commutes with derived scalar extension.
Source: Stacks Project, Tag 0D6D, `lemma-derived-pullback-composition`.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).

Proof:
1. Conjugate the ordinary restriction cube under the geometric and coefficient
   restriction/coextension adjunctions. The two right-adjoint composites agree
   sectionwise, so their conjugates agree.
2. Exact localization preserves this equality. Conjugating with the canonical
   exact/left-derived pullback isomorphisms gives derived_restriction_cube.
3. Paste the coefficient-extension adjunction mates. Compatibility of mates with
   top whiskering gives reverse_scalar_cube for the fixed scalar adjunctions.
4. Cancel the inverse pro-etale scalar comparison and the inverse etale scalar
   comparison. The proved scalarPullbackEtaleIso_eq_fromMate identifies the latter
   with the published representative-normalized Etale.scalarPullbackIso.
This proof applies to every M directly and uses no common flat-model assertion.
It retains the scalar-six unit's etale/pro-etale comparison route and assumes no
finiteness of f, boundedness of M, or flatness of a. -/
theorem etaleProEtale_scalar_pullback_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (scalarPullbackProEtaleIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso A f).hom.app M) ≫
      (pbcComparisonReduction X a).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    L(upperStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction Y a).hom.app M) ≫
      (directImageComparisonAmbientPullbackIso B f).hom.app
        ((pbcFixedScalarExtension Y.smallEtaleTopology a).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.scalarPullbackIso a f).hom.app M)  := by
  have h := reverse_scalar_cube a f M
  have hp := (scalarPullbackReverse_isIso a f).1
  have he := (scalarPullbackReverse_isIso a f).2
  have h' := congrArg (fun z ↦
    (scalarPullbackProEtaleIso a f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫ z ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          ((scalarPullbackEtaleIsoFromMate a f).hom.app M)) h
  simp only [scalarPullbackProEtaleIso, scalarPullbackEtaleIsoFromMate,
    Iso.symm_hom, Category.assoc, ← Functor.map_comp,
    asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id] at h'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
  have hnorm : Etale.scalarPullbackIso a f = scalarPullbackEtaleIsoFromMate a f :=
    scalarPullbackEtaleIso_eq_fromMate a f
  rw [hnorm]
  simpa only [scalarPullbackProEtaleIso, scalarPullbackEtaleIsoFromMate,
    Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] using h'.symm

end AlgebraicGeometry.ProEtale
