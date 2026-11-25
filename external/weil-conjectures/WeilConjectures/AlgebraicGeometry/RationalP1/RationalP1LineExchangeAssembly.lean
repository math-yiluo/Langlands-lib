/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineExchangeSquare
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TraceExchangeFormula
import all WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import all WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.ScalarUnitPullNaturality
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarUnitPush
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The line exchange instance in the rational projective-line square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.MonObj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.RationalP1

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  firstProjection secondProjection square upperStarFromPoint
  DerivedCategory.monoidalClosed Mod.monoidalClosed CondensedRing.upperStar
  Mod.monoidalCategory

set_option allowUnsafeReducibility true in
attribute [local semireducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward

section ProofHelpers
attribute [local irreducible] lineComparison
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal
  CategoryTheory.Monoidal.functorCategorySymmetric

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward

@[instance_reducible]
private def trace_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] trace_sheaf_symmetric

@[instance_reducible]
private def trace_pull_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (CondensedRing.upperStar Λ f).leftDerivedFunctor.CommShift ℤ :=
  CondensedRing.moduleObjectDerivedPullbackCommShift Λ f

@[instance_reducible]
private def trace_push_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor.CommShift ℤ :=
  Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt (CondensedRing.lowerStar Λ f)

@[instance_reducible]
private def trace_scalar_shift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.CommShift ℤ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).leftAdjointCommShift ℤ

attribute [local instance] trace_pull_shift trace_push_shift trace_scalar_shift

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local implicit_reducible] ProEtale.upperStar

-- Lift an ordinary semilinear square through the normalized scalar adjunctions.
private theorem normalized_endpoint_push_square
    {A B A' B' : Type v} [Category.{w} A] [Category.{w} B]
    [Category.{w} A'] [Category.{w} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    [HasDerivedCategory.{z} A'] [HasDerivedCategory.{z} B']
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (U : A' ⥤ A) (V : B' ⥤ B) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (R : DiagonalRightDerived F) (R' : DiagonalRightDerived G)
    (e : G ⋙ V ≅ U ⋙ F)
    (s : DiagonalTrace.ExactSquareOfUniverses G F U V R' R e)
    {EX : DerivedCategory A ⥤ DerivedCategory A'}
    {ES : DerivedCategory B ⥤ DerivedCategory B'}
    (adX : EX ⊣ U.mapDerivedCategory) (adS : ES ⊣ V.mapDerivedCategory)
    {M : B} {M' : B'} {N : A} {N' : A'}
    (x : N ⟶ U.obj N') (y : M ⟶ V.obj M')
    (cX : EX.obj ((DerivedCategory.singleFunctor A 0).obj N) ⟶
      (DerivedCategory.singleFunctor A' 0).obj N')
    (cS : ES.obj ((DerivedCategory.singleFunctor B 0).obj M) ⟶
      (DerivedCategory.singleFunctor B' 0).obj M')
    (hX : adX.homEquiv _ _ cX =
      (DerivedCategory.singleFunctor A 0).map x ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N')
    (hS : adS.homEquiv _ _ cS =
      (DerivedCategory.singleFunctor B 0).map y ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app M')
    (m : M ⟶ F.obj N) (m' : M' ⟶ G.obj N')
    (hm : m ≫ F.map x = y ≫ V.map m' ≫ e.hom.app N') :
    ES.map ((DerivedCategory.singleFunctor B 0).map m ≫ singlePushComparison R N) ≫
        (Adjunction.pushHomOfComapIso adX adS s.iso).app
          ((DerivedCategory.singleFunctor A 0).obj N) ≫ R'.R.map cX =
      cS ≫ (DerivedCategory.singleFunctor B' 0).map m' ≫
        singlePushComparison R' N' := by
  have hs := singlePushComparison_square
    U
    V R' R
    e s N'
  apply (adS.homEquiv _ _).injective
  rw [mate_transpose]
  rw [hX, adS.homEquiv_naturality_right, hS]
  apply (cancel_mono (s.iso.hom.app
    ((DerivedCategory.singleFunctor A' 0).obj N'))).mp
  apply (cancel_mono (R.R.map
    ((U.mapDerivedCategorySingleFunctor
      0).hom.app N'))).mp
  simp only [Category.assoc, Functor.map_comp]
  have hcancel :
      R.R.map ((U.mapDerivedCategorySingleFunctor
        0).inv.app N') ≫
      R.R.map ((U.mapDerivedCategorySingleFunctor
        0).hom.app N') = 𝟙 _ := by
    rw [← R.R.map_comp, Iso.inv_hom_id_app, R.R.map_id]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [hcancel]
  erw [Category.comp_id]
  erw [hs]
  have hn := (V.mapDerivedCategorySingleFunctor
    0).hom.naturality m'
  change V.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor B' 0).map m') ≫
        (V.mapDerivedCategorySingleFunctor 0).hom.app _ =
    (V.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor B 0).map
        (V.map m') at hn
  erw [reassoc_of% hn]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← singlePushComparison_naturality R x]
  have hsingle := congrArg (DerivedCategory.singleFunctor B 0).map hm
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k => k ≫ singlePushComparison R
      (U.obj N')) hsingle

section OrdinaryModuleSquare

set_option allowUnsafeReducibility true in
attribute [local reducible] CondensedRing.lowerStar Mod.comap

-- Forget module structures after taking the geometric adjoints.
private theorem ordinary_adjunct_coefficient_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ S} {N : Modules Λ X} {M' : Modules Λ' S} {N' : Modules Λ' X}
    {mS : M.X ⟶ M'.X} {mX : N.X ⟶ N'.X}
    (cS : Semilinear a M M' mS) (cX : Semilinear a N N' mX)
    (e : (CondensedRing.upperStar Λ f).obj M ⟶ N)
    (e' : (CondensedRing.upperStar Λ' f).obj M' ⟶ N')
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (r' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X)
    (he : ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ e).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r)
    (he' : ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _ e').hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r')
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ r' = r ≫ mX) :
    (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ e ≫
        (CondensedRing.lowerStar Λ f).map cX.hom =
      cS.hom ≫ (Mod.comap (coefficientMap a S)).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _ e') ≫
      (CondensedRing.comapLowerStarIso a f).hom.app N' := by
  apply Mod.hom_ext
  change
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ e).hom ≫
      (lowerStar Ab.{u + 1} f).map cX.hom.hom =
    cS.hom.hom ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _ e').hom ≫
        ((CondensedRing.comapLowerStarIso a f).hom.app N').hom
  rw [he, he', cS.underlying, cX.underlying]
  rw [CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
  with_unfolding_all
    change (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r ≫
        (lowerStar Ab.{u + 1} f).map mX =
      mS ≫ (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r' ≫ 𝟙 _
  rw [Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  exact congrArg ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _) hr.symm

end OrdinaryModuleSquare

-- Normalize the dependent module categories and their canonical derived comparisons.
private theorem pull_single_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (e : (CondensedRing.upperStar Λ f).obj M ⟶ N) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
        (((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.app M).hom ≫
          (DerivedCategory.singleFunctor (Modules Λ X) 0).map e) =
      (DerivedCategory.singleFunctor (Modules Λ S) 0).map
          ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ e) ≫
        singlePushComparison (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f))
          N := by
  let ad := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  let ad' := (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (CondensedRing.upperStarLowerStarAdjunction Λ f)).ofNatIsoLeft
        (Functor.leftDerivedFunctorIsoMapDerivedCategory
          (CondensedRing.upperStar Λ f)).symm
  have ha : ad = ad' := by
    dsimp [ad, ad']
    unfold CondensedRing.derivedUpperStarLowerStarAdjunction
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (CondensedRing.upperStar Λ f)).symm
  change ad.homEquiv _ _ _ = _
  rw [ha, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have h := DiagonalTrace.adjunct_single
    (CondensedRing.upperStarLowerStarAdjunction Λ f) M N e
  rw [DiagonalTrace.rightSingle_eq] at h
  unfold singlePushComparison
  coefficient_finish h

-- Normalize the canonical single-complex scalar and geometric adjunctions.
private theorem unshifted_endpoint_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ S} {N : Modules Λ X} {M' : Modules Λ' S} {N' : Modules Λ' X}
    {mS : M.X ⟶ M'.X} {mX : N.X ⟶ N'.X}
    (cS : Endpoint a M M' mS) (cX : Endpoint a N N' mX)
    (e : (CondensedRing.upperStar Λ f).obj M ⟶ N)
    (e' : (CondensedRing.upperStar Λ' f).obj M' ⟶ N')
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (r' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X)
    (he : ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ e).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r)
    (he' : ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _ e').hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ r')
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ r' = r ≫ mX) :
    PullEndpointSquare (derivedPullIso a f).hom cS.iso.hom
      (((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.app M).hom ≫
        (DerivedCategory.singleFunctor (Modules Λ X) 0).map e)
      (((CondensedRing.upperStar Λ' f).singleFunctorCompLeftDerivedFunctorIso.app M').hom ≫
        (DerivedCategory.singleFunctor (Modules Λ' X) 0).map e') cX.iso.hom := by
  let R := canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f)
  let R' := canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f)
  let s : RestrictionSquare a f R R' :=
    { iso := derivedComapLowerStarIso a f
      normalization := by
        intro P
        have h := canonicalSquare_normalization
          (CondensedRing.lowerStar Λ' f) (CondensedRing.lowerStar Λ f)
          (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
          (comapLowerStarIso a f) P
        unfold derivedComapLowerStarIso
        coefficient_finish h }
  have hp := normalized_endpoint_push_square
    (CondensedRing.lowerStar Λ f) (CondensedRing.lowerStar Λ' f)
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
    R R' (CondensedRing.comapLowerStarIso a f) s
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    cX.semilinear.hom cS.semilinear.hom cX.iso.hom cS.iso.hom
    cX.normalization cS.normalization
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
      e)
    ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _
      e')
    (ordinary_adjunct_coefficient_square a f cS.semilinear cX.semilinear
      e e' r r' he he' hr)
  rw [← pull_single_adjunct Λ f M N
      e,
    ← pull_single_adjunct Λ' f M' N'
      e'] at hp
  have h := pull_endpoint_of_push
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f)
    (derivedComapLowerStarIso a f) cS.iso.hom
    (((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.app M).hom ≫
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map e)
    (((CondensedRing.upperStar Λ' f).singleFunctorCompLeftDerivedFunctorIso.app M').hom ≫
      (DerivedCategory.singleFunctor (Modules Λ' X) 0).map e') cX.iso.hom
    (by coefficient_finish hp)
  unfold PullEndpointSquare derivedPullIso
  coefficient_finish h

-- Keep coefficient selectors abstract while specializing the normalized square.
private theorem option_unshifted_line_square
    (l : ℕ) [Fact l.Prime] (c c' : Option (PadicAlgCl.FiniteIntermediateField l))
    (a : (coefficient.{u} l c).X ⟶ (coefficient l c').X) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    {mS : (line l c S).X ⟶ (line l c' S).X}
    {mX : (line l c X).X ⟶ (line l c' X).X}
    (cS : Endpoint a (line l c S) (line l c' S) mS)
    (cX : Endpoint a (line l c X) (line l c' X) mX)
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ abelianComparison l c' f =
      abelianComparison l c f ≫ mX) :
    PullEndpointSquare (derivedPullIso a f).hom cS.iso.hom
      (((Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar (coefficient l c).X f)).app (line l c S)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (lineComparison l c f).hom)
      (((Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar (coefficient l c').X f)).app (line l c' S)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (lineComparison l c' f).hom)
      cX.iso.hom := by
  exact unshifted_endpoint_square a f cS cX
    (lineComparison l c f).hom (lineComparison l c' f).hom
    (abelianComparison l c f) (abelianComparison l c' f)
    (lineComparison_adjunct l c f) (lineComparison_adjunct l c' f) hr

-- Shift a commuting square using the four functors' canonical shift comparisons.
private theorem shift_endpoint_square
    {C D C' D' : Type w} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {H : C ⥤ D} {He : C' ⥤ D'} {T : C ⥤ C'} {U : D ⥤ D'}
    [H.CommShift ℤ] [He.CommShift ℤ] [T.CommShift ℤ] [U.CommShift ℤ]
    (α : H ⋙ U ⟶ T ⋙ He) [NatTrans.CommShift α ℤ]
    {K : C} {K' : C'} {W : D} {W' : D'}
    (cK : T.obj K ⟶ K') (e : H.obj K ⟶ W) (e' : He.obj K' ⟶ W')
    (cW : U.obj W ⟶ W') (n : ℤ)
    (h : PullEndpointSquare α cK e e' cW) :
    PullEndpointSquare α
      ((T.commShiftIso n).hom.app K ≫ (shiftFunctor C' n).map cK)
      ((H.commShiftIso n).hom.app K ≫ (shiftFunctor D n).map e)
      ((He.commShiftIso n).hom.app K' ≫ (shiftFunctor D' n).map e')
      ((U.commShiftIso n).hom.app W ≫ (shiftFunctor D' n).map cW) := by
  unfold PullEndpointSquare at h ⊢
  have hs := NatTrans.shift_app_comm α n K
  simp only [Functor.commShiftIso_comp_hom_app] at hs
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (He.commShiftIso_hom_naturality cK n)]
  rw [← reassoc_of% hs]
  have h' := congrArg (shiftFunctor D' n).map h
  simp only [Functor.map_comp] at h'
  rw [h']
  rw [← reassoc_of% (U.commShiftIso_hom_naturality e n)]

-- Normalize the dependent module categories and their canonical derived comparisons.
private theorem scalar_pull_shift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift
      (show moduleObjectDerivedPullback Λ f ⋙ derivedScalars a X ⟶
        derivedScalars a S ⋙ moduleObjectDerivedPullback Λ' f from
          (derivedPullIso a f).hom) ℤ := by
  have := rightCompExactIso_shift (CondensedRing.lowerStar Λ' f)
    (Mod.comap (coefficientMap a S))
  have := rightNatIso_shift (CondensedRing.comapLowerStarIso a f)
  have := rightCompIso_shift (Mod.comap (coefficientMap a X))
    (CondensedRing.lowerStar Λ f)
  have := rightExactIso_shift
    (Mod.comap (coefficientMap a X) : Modules Λ' X ⥤ Modules Λ X)
  have hr : NatTrans.CommShift (derivedComapLowerStarIso a f).hom ℤ := by
    unfold derivedComapLowerStarIso
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  have := CondensedRing.derivedAdjunction_shift Λ f
  have := CondensedRing.derivedAdjunction_shift Λ' f
  have : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).commShift_of_rightAdjoint ℤ
  have : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a S)).CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a S)).commShift_of_rightAdjoint ℤ
  have hcomp : ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a S)).comp
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f)).CommShift ℤ := by
    exact Adjunction.CommShift.instComp
      (adj := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
      (adj' := CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f) (A := ℤ)
  have hcomp' : ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).CommShift ℤ := by
    exact Adjunction.CommShift.instComp
      (adj := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
      (adj' := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)) (A := ℤ)
  unfold derivedPullIso Adjunction.pullIsoOfComapIso
  exact @inverseConjugate_shift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomp hcomp' _ hr

-- The shifted root-line comparisons are the preceding degree-zero comparisons.
private theorem option_shifted_line_square
    (l : ℕ) [Fact l.Prime] (c c' : Option (PadicAlgCl.FiniteIntermediateField l))
    (a : (coefficient.{u} l c).X ⟶ (coefficient l c').X) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    {mS : (line l c S).X ⟶ (line l c' S).X}
    {mX : (line l c X).X ⟶ (line l c' X).X}
    (cS : Endpoint a (line l c S) (line l c' S) mS)
    (cX : Endpoint a (line l c X) (line l c' X) mX)
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ abelianComparison l c' f =
      abelianComparison l c f ≫ mX) :
    PullEndpointSquare (derivedPullIso a f).hom (cS.shift a)
      (shiftedLineComparison l c f).hom (shiftedLineComparison l c' f).hom
      (cX.shift a) := by
  let α := (derivedPullIso a f).hom
  have : NatTrans.CommShift α ℤ := scalar_pull_shift a f
  let e := (Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar (coefficient l c).X f)).app (line l c S) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (lineComparison l c f)
  let e' := (Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar (coefficient l c').X f)).app (line l c' S) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (lineComparison l c' f)
  have h0 : PullEndpointSquare α cS.iso.hom e.hom e'.hom cX.iso.hom :=
    option_unshifted_line_square l c c' a f cS cX hr
  have h := shift_endpoint_square α cS.iso.hom e.hom e'.hom cX.iso.hom (2 : ℤ) h0
  unfold PullEndpointSquare at h ⊢
  unfold Endpoint.shift shiftedLineComparison
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  coefficient_finish h

-- Identify the native exchange wrappers with the fixed coefficient functors.
private theorem option_exchange_paste
    (l : ℕ) [Fact l.Prime] (c c' : Option (PadicAlgCl.FiniteIntermediateField l))
    (a : (coefficient.{u} l c).X ⟶ (coefficient l c').X) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    {mP : (line l c (ProjectiveLine Y)).X ⟶ (line l c' (ProjectiveLine Y)).X}
    {mW : (line l c (diagonalSurface Y)).X ⟶ (line l c' (diagonalSurface Y)).X}
    (cP : Endpoint a (line l c (ProjectiveLine Y)) (line l c' (ProjectiveLine Y)) mP)
    (cW : Endpoint a (line l c (diagonalSurface Y)) (line l c' (diagonalSurface Y)) mW)
    (he : PullEndpointSquare (derivedPullIso a (firstProjection Y)).hom
      (cP.shift a) (firstLineComparisonForTrace l c k p hpl Y).hom
      (firstLineComparisonForTrace l c' k p hpl Y).hom (cW.shift a)) :
    PullArrowSquare (derivedPullIso a (ProjectiveLine Y ↘ Y))
      ((derivedPushHom a (ProjectiveLine Y ↘ Y)).app _ ≫
        (moduleObjectDerivedPushforward (coefficient l c').X (ProjectiveLine Y ↘ Y)).map
          (cP.shift a))
      (secondTraceExchange l c k p hpl Y) (secondTraceExchange l c' k p hpl Y)
      ((derivedPushHom a (secondProjection Y)).app _ ≫
        (moduleObjectDerivedPushforward (coefficient l c').X (secondProjection Y)).map
          (cW.shift a)) := by
  rw [secondTraceExchange_eq_native, secondTraceExchange_eq_native]
  have h := coefficient_exchange_line
    (condensedAmbientExchange (coefficient l c).X (square Y))
    (condensedAmbientExchange (coefficient l c').X (square Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y)) (derivedPullIso a (firstProjection Y)).hom
    (derivedPushHom a (ProjectiveLine Y ↘ Y)) (derivedPushHom a (secondProjection Y))
    (cP.shift a) (firstLineComparisonForTrace l c k p hpl Y).hom
    (firstLineComparisonForTrace l c' k p hpl Y).hom (cW.shift a)
    (flat_coefficient_exchange a (square Y) _) he
  unfold PullArrowSquare at h ⊢
  coefficient_finish h

end ProofHelpers

-- Assemble and normalize the exchange before specializing the coefficient rings.
private theorem option_line_exchange_square
    (l : ℕ) [Fact l.Prime] (c c' : Option (PadicAlgCl.FiniteIntermediateField l))
    (a : (coefficient.{u} l c).X ⟶ (coefficient l c').X) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    {mP : (line l c (ProjectiveLine Y)).X ⟶ (line l c' (ProjectiveLine Y)).X}
    {mW : (line l c (diagonalSurface Y)).X ⟶ (line l c' (diagonalSurface Y)).X}
    (cP : Endpoint a (line l c (ProjectiveLine Y)) (line l c' (ProjectiveLine Y)) mP)
    (cW : Endpoint a (line l c (diagonalSurface Y)) (line l c' (diagonalSurface Y)) mW)
    (he : PullEndpointSquare (derivedPullIso a (firstProjection Y)).hom
      (cP.shift a) (firstLineComparisonForTrace l c k p hpl Y).hom
      (firstLineComparisonForTrace l c' k p hpl Y).hom (cW.shift a)) :
    PullArrowSquare (derivedPullIso a (ProjectiveLine Y ↘ Y))
      ((derivedPushHom a (ProjectiveLine Y ↘ Y)).app _ ≫
        (moduleObjectDerivedPushforward (coefficient l c').X (ProjectiveLine Y ↘ Y)).map
          (cP.shift a))
      (secondTraceExchange l c k p hpl Y) (secondTraceExchange l c' k p hpl Y)
      ((derivedPushHom a (secondProjection Y)).app _ ≫
        (moduleObjectDerivedPushforward (coefficient l c').X (secondProjection Y)).map
          (cW.shift a)) := by
  have h := option_exchange_paste l c c' a k p hpl Y cP cW he
  unfold PullArrowSquare at h ⊢
  coefficient_finish h

-- At concrete selectors, use the existing monoid and flatness instances of the fields.
set_option allowUnsafeReducibility true in
attribute [local reducible] coefficient

-- Transport the concrete coefficient categories without unfolding their derived models.
/-- The native coefficient exchange transports to the two shifted root-line maps, giving the
line exchange square for the rational projective line. -/
theorem rational_p1_line_exchange_assembly
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (cP : Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist (ProjectiveLine Y) l E) (spQbarTwist (ProjectiveLine Y) l)
      (closureLineMap l E (ProjectiveLine Y)))
    (cW : Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist (diagonalSurface Y) l E) (spQbarTwist (diagonalSurface Y) l)
      (closureLineMap l E (diagonalSurface Y))) :
    LineExchangeSquare l E k p hpl Y cP cW := by
  let a : (coefficient.{u} l (some E)).X ⟶ (coefficient l none).X :=
    Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
  let : IsMonHom a := by dsimp only [a, coefficient]; infer_instance
  let : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap a Z)) := by
    intro Z
    dsimp only [a, coefficient]
    exact CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      l Z E
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  have he := option_shifted_line_square l (some E) none a (firstProjection Y) cP cW
    (by
      dsimp only [abelianComparison]
      exact (adicComparison l (firstProjection Y)).qbar_coprojection E)
  have h := option_line_exchange_square l (some E) none a k p hpl Y cP cW (by
    unfold firstLineComparisonForTrace
    unfold PullEndpointSquare at he ⊢
    coefficient_finish he)
  unfold LineExchangeSquare finiteSecondTraceExchange closureSecondTraceExchange
  unfold PullArrowSquare at h ⊢
  dsimp only [coefficient, line] at h
  exact h

end AlgebraicGeometry.ProEtale.RationalP1
