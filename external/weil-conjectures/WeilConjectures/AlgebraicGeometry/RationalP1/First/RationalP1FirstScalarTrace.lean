/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralLinePullIso
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction
import all WeilConjectures.AlgebraicGeometry.InternalScalarRegularPullCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.NatIso
import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeConjugate
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPullbackCompatibility
import all WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedScalarChernModel
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Scalar base change for the first projective-line trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal SymmetricCategory.ofCurried
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 21000] CondensedRing.monoidal_upperStar
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

@[instance_reducible]
private def trace_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] trace_sheaf_symmetric

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction Mod.monoidalCategory Mod.monoidalClosed
set_option allowUnsafeReducibility true in
attribute [local reducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
  derivedUpper derivedLower derivedScalars internalScalarExtension Mod.regular
  internalMonoidal internalTensorBundle nativeTensorBundle
attribute [local irreducible] square
attribute [local irreducible] condensedAmbientPullbackComparison

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

-- Compare the full derived-unit normalization before cancelling the single comparison.
private theorem endpoint_hom
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X : Scheme.{u}} {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (e : Endpoint a M N m) :
    e.iso.hom =
      (Mod.extendScalars (coefficientMap a X)).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
        (DerivedCategory.singleFunctor (Modules Λ' X) 0).map
          (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv M N).symm
            e.semilinear.hom) := by
  let b := Mod.extendRestrictAdjunction (coefficientMap a X)
  let v := (b.homEquiv M N).symm e.semilinear.hom
  let t :=
    (Mod.extendScalars (coefficientMap a X)).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
      (DerivedCategory.singleFunctor (Modules Λ' X) 0).map v
  apply ((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a X)).homEquiv _ _).injective
  have hn : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).homEquiv _ _ e.iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map e.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N := by
    have hh := e.normalization
    coefficient_finish hh
  have hv : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).homEquiv _ _ t ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map e.semilinear.hom := by
    have h := Adjunction.derivedSingleUnit_comp_comparison b M N v
    dsimp only [v] at h
    rw [Equiv.apply_symm_apply] at h
    have ht : (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap a X)).homEquiv _ _ t ≫
          ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app N =
        Adjunction.derivedSingleUnit b M N v ≫
          (Mod.comap (coefficientMap a X)).singleFunctorCompRightDerivedFunctorIso.hom.app N := by
      simp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
        Adjunction.homEquiv_ofNatIsoRight_apply, Category.assoc,
        Functor.singleFunctorCompRightDerivedFunctorIso,
        Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app]
      simp only [Adjunction.derivedSingleUnit_eq, Mod.derivedExtendRestrictAdjunction,
        Mod.rightDerivedComapIsoMapDerivedCategory, Adjunction.homEquiv_unit, b, t,
        Category.assoc]
    exact ht.trans h
  let c := ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).app N
  exact hn.trans ((c.eq_comp_inv).2 hv).symm

-- Keep both composite adjunctions fixed while identifying the normalized conjugate.
private theorem derivedPull_eq_path
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    derivedPullIso a f =
      ((CondensedRing.upperStar Λ f).leftDerivedFunctorCompIso
        (Mod.extendScalars (coefficientMap a X))).symm ≪≫
      Functor.leftDerivedFunctorNatIso _ (CondensedRing.pullIso a f) ≪≫
      (Mod.extendScalars (coefficientMap a S)).leftDerivedFunctorCompIso
        (CondensedRing.upperStar Λ' f) := by
  have h := path_conjugate a f
  have he : coefficientScalarPathIso a f = (derivedPullIso a f).symm := by
    apply Iso.ext
    apply (conjugateEquiv
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)).comp
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f))).injective
    exact h.trans ((conjugateEquiv _ _).apply_symm_apply _).symm
  have hh := congrArg Iso.symm he
  have hl : derivedPullIso a f = (coefficientScalarPathIso a f).symm :=
    (Iso.symm_symm_eq (derivedPullIso a f)).symm.trans hh.symm
  refine Eq.trans hl ?_
  simp only [coefficientScalarPathIso, Functor.leftDerivedFunctorCompNatIso,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  have hi := Functor.leftDerivedFunctorNatIso_symm
    (CondensedRing.upperStar Λ f ⋙ Mod.extendScalars (coefficientMap a X))
    (CondensedRing.pullIso a f)
  have hsym := congrArg
    (fun z ↦ ((CondensedRing.upperStar Λ f).leftDerivedFunctorCompIso
        (Mod.extendScalars (coefficientMap a X))).symm ≪≫ z.symm ≪≫
      (Mod.extendScalars (coefficientMap a S)).leftDerivedFunctorCompIso
        (CondensedRing.upperStar Λ' f)) hi
  simp only [Iso.symm_symm_eq] at hsym
  coefficient_finish hsym

section OrdinaryEndpointSquare

set_option allowUnsafeReducibility true in
attribute [local reducible] CondensedRing.lowerStar Mod.comap

-- Transpose the module square twice without expanding sheafification data.
private theorem ordinary_endpoint_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ S} {N : Modules Λ X} {M' : Modules Λ' S} {N' : Modules Λ' X}
    {mS : M.X ⟶ M'.X} {mX : N.X ⟶ N'.X}
    {r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    {r' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X}
    (cS : Semilinear a M M' mS) (cX : Semilinear a N N' mX)
    (e : PullEndpoint Λ f M N r) (e' : PullEndpoint Λ' f M' N' r')
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ r' = r ≫ mX) :
    (CondensedRing.pullIso a f).hom.app M ≫
        (CondensedRing.upperStar Λ' f).map
          (((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv M M').symm cS.hom) ≫
        e'.iso.hom =
      (Mod.extendScalars (coefficientMap a X)).map e.iso.hom ≫
        (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv N N').symm cX.hom) := by
  apply (cancel_epi ((CondensedRing.pullIso a f).inv.app M)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (((Mod.extendRestrictAdjunction (coefficientMap a S)).comp
    (CondensedRing.upperStarLowerStarAdjunction Λ' f)).homEquiv _ _).injective
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  -- Reassociate the two transpositions into the order of the composite adjunction.
  rw [Adjunction.homEquiv_naturality_left]
  unfold CondensedRing.pullIso
  rw [Adjunction.homEquiv_homEquiv_pullIsoOfComapIso_inv]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  have hi : ((CondensedRing.comapLowerStarIso a f).inv.app N').hom = 𝟙 _ := by
    have hh := congrArg Mod.Hom.hom
      ((CondensedRing.comapLowerStarIso a f).hom_inv_id_app N')
    simp only [Mod.comp_hom', Mod.id_hom', CondensedRing.comapLowerStarIso,
      Mod.comapMapModComapIso_hom_app_hom] at hh
    erw [Category.id_comp] at hh
    exact hh
  apply Mod.hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom, hi, e.normalization,
    e'.normalization, cS.underlying, cX.underlying]
  have hh := congrArg ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _) hr
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
  exact hh

end OrdinaryEndpointSquare

-- Identify the two exact-derived composition paths on a single module.
private theorem derivedPull_single
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules Λ S) :
    (derivedPullIso a f).hom.app ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ≫
        (CondensedRing.upperStar Λ' f).leftDerivedFunctor.map
          ((Mod.extendScalars (coefficientMap a S)).singleFunctorCompLeftDerivedFunctorIso.hom.app
            M) ≫
        (CondensedRing.upperStar Λ' f).singleFunctorCompLeftDerivedFunctorIso.hom.app _ =
      (derivedScalars a X).map
          ((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
        (Mod.extendScalars (coefficientMap a X)).singleFunctorCompLeftDerivedFunctorIso.hom.app _ ≫
        (DerivedCategory.singleFunctor (Modules Λ' X) 0).map
          ((CondensedRing.pullIso a f).hom.app M) := by
  apply (cancel_epi (((CondensedRing.upperStar Λ f).leftDerivedFunctorCompIso
    (Mod.extendScalars (coefficientMap a X))).hom.app _)).1
  rw [derivedPull_eq_path a f]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (Mod.extendScalars (coefficientMap a S)) (CondensedRing.upperStar Λ' f) M]
  rw [Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar Λ f ⋙ Mod.extendScalars (coefficientMap a X))
    (Mod.extendScalars (coefficientMap a S) ⋙ CondensedRing.upperStar Λ' f)
    (CondensedRing.pullIso a f) M]
  rw [reassoc_of% (Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar Λ f) (Mod.extendScalars (coefficientMap a X)) M)]

-- Paste naturality squares before specializing to the concrete derived functors.
private theorem comparison_endpoint_paste
    {B C D B' C' D' : Type*}
    [Category B] [Category C] [Category D] [Category B'] [Category C'] [Category D']
    (G : B ⥤ D) (I : C ⥤ D) (SB : B ⥤ B') (SC : C ⥤ C') (SD : D ⥤ D')
    (LG : B' ⥤ D') (LI : C' ⥤ D')
    (cG : SB ⋙ LG ⟶ G ⋙ SD) (cI : SC ⋙ LI ⟶ I ⋙ SD)
    {M N : B} {M' N' : C} {Q : D} {K : D'}
    (x : K ⟶ LG.obj (SB.obj M)) (y : K ⟶ LI.obj (SC.obj M'))
    (c : G.obj M ⟶ I.obj M') (e : M ⟶ N) (m : M' ⟶ N')
    (n : G.obj N ⟶ Q) (r : I.obj N' ⟶ Q)
    (hc : y ≫ cI.app M' = x ≫ cG.app M ≫ SD.map c)
    (ho : c ≫ I.map m ≫ r = G.map e ≫ n) :
    y ≫ LI.map (SC.map m) ≫ cI.app N' ≫ SD.map r =
      x ≫ LG.map (SB.map e) ≫ cG.app N ≫ SD.map n := by
  have hi := cI.naturality m
  have hg := cG.naturality e
  dsimp only [Functor.comp_map] at hi hg
  rw [reassoc_of% hi, reassoc_of% hc]
  have hh := congrArg SD.map ho
  simp only [Functor.map_comp] at hh
  rw [hh, ← reassoc_of% hg]

-- Normalize both scalar endpoints and paste the exact single comparisons.
private theorem endpoint_pull_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ S} {N : Modules Λ X} {M' : Modules Λ' S} {N' : Modules Λ' X}
    {mS : M.X ⟶ M'.X} {mX : N.X ⟶ N'.X}
    {r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    {r' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X}
    (cS : Endpoint a M M' mS) (cX : Endpoint a N N' mX)
    (e : PullEndpoint Λ f M N r) (e' : PullEndpoint Λ' f M' N' r')
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ r' = r ≫ mX) :
    (derivedPullIso a f).hom.app ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ≫
        (derivedUpper Λ' f).map cS.iso.hom ≫ e'.derived =
      (derivedScalars a X).map e.derived ≫ cX.iso.hom := by
  have h := comparison_endpoint_paste
    (Mod.extendScalars (coefficientMap a X)) (CondensedRing.upperStar Λ' f)
    (DerivedCategory.singleFunctor (Modules Λ X) 0)
    (DerivedCategory.singleFunctor (Modules Λ' S) 0)
    (DerivedCategory.singleFunctor (Modules Λ' X) 0)
    (derivedScalars a X) (derivedUpper Λ' f)
    (Mod.extendScalars (coefficientMap a X)).singleFunctorCompLeftDerivedFunctorIso.hom
    (CondensedRing.upperStar Λ' f).singleFunctorCompLeftDerivedFunctorIso.hom
    ((derivedScalars a X).map
      ((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app M))
    ((derivedPullIso a f).hom.app ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ≫
      (derivedUpper Λ' f).map
        ((Mod.extendScalars (coefficientMap a S)).singleFunctorCompLeftDerivedFunctorIso.hom.app M))
    ((CondensedRing.pullIso a f).hom.app M) e.iso.hom
    (((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv M M').symm
      cS.semilinear.hom)
    (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv N N').symm
      cX.semilinear.hom) e'.iso.hom
    (by simpa only [Category.assoc] using derivedPull_single a f M)
    (ordinary_endpoint_square a f cS.semilinear cX.semilinear e e' hr)
  rw [endpoint_hom a cS, endpoint_hom a cX]
  unfold PullEndpoint.derived singlePullback
  simpa only [Functor.map_comp, Category.assoc, Iso.app_hom] using h

-- Supply the shift compatibilities of the full derived composite adjunctions.
private theorem derivedPull_commShift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift (derivedPullIso a f).hom ℤ := by
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

private theorem shifted_pull_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (F : C ⥤ D) (F' : C' ⥤ D') (T : C ⥤ C') (U : D ⥤ D')
    [F.CommShift ℤ] [F'.CommShift ℤ] [T.CommShift ℤ] [U.CommShift ℤ]
    (α : F ⋙ U ≅ T ⋙ F') [NatTrans.CommShift α.hom ℤ]
    {M : C} {N : D} {M' : C'} {N' : D'}
    (m : T.obj M ⟶ M') (n : U.obj N ⟶ N')
    (e : F.obj M ⟶ N) (e' : F'.obj M' ⟶ N')
    (h : α.hom.app M ≫ F'.map m ≫ e' = U.map e ≫ n) (i : ℤ) :
    α.hom.app (M⟦i⟧) ≫
        F'.map ((T.commShiftIso i).hom.app M ≫ m⟦i⟧') ≫
        (F'.commShiftIso i).hom.app M' ≫ e'⟦i⟧' =
      U.map ((F.commShiftIso i).hom.app M ≫ e⟦i⟧') ≫
        (U.commShiftIso i).hom.app N ≫ n⟦i⟧' := by
  have hm := (F'.commShiftIso i).hom.naturality m
  have he := (U.commShiftIso i).hom.naturality e
  dsimp only [Functor.comp_map, Functor.comp_obj] at hm he
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hm]
  have ha := NatTrans.shift_app_comm α.hom i M
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at ha
  rw [← reassoc_of% ha]
  have hh := congrArg (fun z ↦ (shiftFunctor D' i).map z) h
  simp only [Functor.map_comp] at hh
  rw [hh, ← reassoc_of% he]

private theorem pullbackShift_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) (i : ℤ) :
    (letI := derivedUpperCommShift Λ f;
      (derivedUpper Λ f).commShiftIso i) =
      (letI := CondensedRing.moduleObjectDerivedPullbackCommShift Λ f;
        (moduleObjectDerivedPullback Λ f).commShiftIso i) := by
  have : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).CommShift ℤ := by
    exact CondensedRing.derivedAdjunction_shift Λ f
  change Adjunction.LeftAdjointCommShift.iso
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f) i = _
  exact Adjunction.CommShift.compatibilityUnit_unique_left
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f) _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso _ i)
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).shift_unit_app i)

/-- The endpoint map with its source fixed in the native pullback functor. -/
private def nativePullEndpointShift
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m) :
    (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj N) ⟦(2 : ℤ)⟧ := e.shift

private theorem nativePullEndpointShift_formula
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m) :
    nativePullEndpointShift e =
      ((moduleObjectDerivedPullback Λ f).commShiftIso (2 : ℤ)).hom.app _ ≫
        (shiftFunctor _ (2 : ℤ)).map
          ((singlePullback Λ f M).hom ≫
            (DerivedCategory.singleFunctor (Modules Λ X) 0).map e.iso.hom) := by
  unfold nativePullEndpointShift PullEndpoint.shift PullEndpoint.derived
  rw [pullbackShift_eq]

-- Transport the normalized endpoint square through the specified shift structures.
private theorem endpoint_pull_square_shift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ S} {N : Modules Λ X} {M' : Modules Λ' S} {N' : Modules Λ' X}
    {mS : M.X ⟶ M'.X} {mX : N.X ⟶ N'.X}
    {r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    {r' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X}
    (cS : Endpoint a M M' mS) (cX : Endpoint a N N' mX)
    (e : PullEndpoint Λ f M N r) (e' : PullEndpoint Λ' f M' N' r')
    (hr : (upperStar Ab.{u + 1} f).map mS ≫ r' = r ≫ mX) :
    PullEndpointSquare (derivedPullIso a f).hom (cS.shift a) e.shift e'.shift
      (cX.shift a) := by
  have := derivedPull_commShift a f
  unfold PullEndpointSquare PullEndpoint.shift
  rw [pullbackShift_eq, pullbackShift_eq]
  have h := shifted_pull_square _ _ _ _ (derivedPullIso a f) cS.iso.hom cX.iso.hom
    e.derived e'.derived (endpoint_pull_square a f cS cX e e' hr) (2 : ℤ)
  coefficient_finish h

private theorem extensionUnit_pull_natural
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers C] [HasCoequalizers D]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    [∀ Z : D, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (F : C ⥤ D) [F.Monoidal]
    {R A : C} [MonObj R] [MonObj A] [IsCommMonObj R]
    {S B : D} [MonObj S] [MonObj B] [IsCommMonObj S]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (c : F.obj A ⟶ B) [IsMonHom c] (M : Mod C R) (N : Mod D S)
    (g : F.obj M.X ⟶ N.X)
    (r : F.obj (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X)
    (h : F.map (Mod.extendπ p M) ≫ r =
      Functor.OplaxMonoidal.δ F A M.X ≫ (c ⊗ₘ g) ≫ Mod.extendπ q N) :
    F.map (Mod.extendUnitHom p M) ≫ r = g ≫ Mod.extendUnitHom q N := by
  have hc : F.map η[A] ≫ c = Functor.OplaxMonoidal.η F ≫ η[B] := by
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
    rw [← Category.assoc]
    change η[F.obj A] ≫ c = _
    rw [IsMonHom.one_hom, Functor.Monoidal.ε_η_assoc]
  simp only [Mod.extendUnitHom, Functor.map_comp, Category.assoc]
  rw [h, ← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, hc, comp_whiskerRight_assoc]
  rw [← Functor.OplaxMonoidal.left_unitality_assoc]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

private theorem rational_root_scalar_square (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (upperStar Ab.{u + 1} f).map (rationalLineMap l E S) ≫
        (adicComparison l f).rational E =
      spIntegralComparison f l E ≫ rationalLineMap l E X := by
  exact extensionUnit_pull_natural (upperStar Ab.{u + 1} f)
    (padicIntegersToPadicSubfield S l E) (padicIntegersToPadicSubfield X l E)
    (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f)
    (spIntegralTwist S l E) (spIntegralTwist X l E)
    (spIntegralComparison f l E) ((adicComparison l f).rational E)
    ((adicComparison l f).rational_scalar E)

section NativeUnits
set_option allowUnsafeReducibility true in
attribute [local reducible] Mod.monoidalCategory Mod.derivedMonoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory trace_sheaf_symmetric
  CondensedRing.lowerStar Mod.comap Mod.forget
attribute [local semireducible] Mod.monoidalClosed
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] Mod.monoidalCategory Mod.derivedMonoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem singleUnitIso_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (singleUnitIso Λ X).hom = 𝟙 _ := by
  have h := (singleUnit_existsUnique Λ X).exists.choose_spec
  unfold internalMonoidal internalTensorBundle nativeTensorBundle at *
  rw [show singleUnitIso Λ X = DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)
    from eq_of_heq h]
  exact SheafExactDegreeZero.single_unit_hom

private theorem singleUnitIso_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (singleUnitIso Λ X).inv = 𝟙 _ := by
  have h := (singleUnit_existsUnique Λ X).exists.choose_spec
  unfold internalMonoidal internalTensorBundle nativeTensorBundle at *
  rw [show singleUnitIso Λ X = DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)
    from eq_of_heq h]
  exact SheafExactDegreeZero.single_unit_inv

private theorem singlePullback_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (singlePullback Λ f (Mod.regular (condensedRingObj Λ S))).hom ≫
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv =
      (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom := by
  unfold singlePullback
  exact (QuotientChange.exact_unit Λ f).symm

private def nativeUnitPullEndpoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    UnitPullEndpoint Λ f where
  iso := (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm
  normalization := by
    have hu : condensedPushforwardHom Λ f =
        ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _)
          (condensedPullbackHom Λ f) := by
      rw [Adjunction.homEquiv_unit]
      rfl
    erw [CondensedRing.homEquiv_εIso_inv_hom Λ f]
    exact hu

-- Compare the normalized degree-zero unit with the native monoidal unit map.
private theorem unitPullEndpoint_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (e : UnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)) :
    e.derived = (scalarUnitPullIso Λ Y).hom := by
  have he' : e.iso.hom =
      (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)).iso.hom := by
    apply ((CondensedRing.upperStarLowerStarAdjunction Λ
      (ProjectiveLine Y ↘ Y)).homEquiv _ _).injective
    apply Mod.hom_ext
    erw [e.normalization,
      (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)).normalization]
  have he : e.iso.hom =
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y))).inv := by
    dsimp only [nativeUnitPullEndpoint, Iso.symm_hom] at he'
    exact he'
  unfold PullEndpoint.derived
  erw [he, singlePullback_unit]
  unfold scalarUnitPullIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [singleUnitIso_hom, singleUnitIso_inv]
  erw [(moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map_id (unit Λ Y)]
  erw [Category.id_comp, Category.comp_id]
  unfold secondTraceUnitIso secondTracePullMonoidal moduleObjectDerivedPullback
  rfl

end NativeUnits

private theorem derivedCongr_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (f g : X ⟶ S) (h : f = g) :
    Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr Λ h) =
      eqToIso (congrArg (fun a : X ⟶ S ↦
        (CondensedRing.upperStar Λ a).leftDerivedFunctor) h) := by
  subst g
  simp only [CondensedRing.upperStarCongr_self, Functor.leftDerivedFunctorNatIso]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_refl,
    Category.id_comp, Iso.hom_inv_id, eqToIso_refl, Iso.refl_hom]

private theorem unit_pull_scalar
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (cY : Endpoint a (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ' Y)) (coefficientMap a Y))
    (cP : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y))) :
    (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom.app (unit Λ Y) ≫
        (moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y)).map cY.iso.hom ≫
          (scalarUnitPullIso Λ' Y).hom =
      (derivedScalars a (ProjectiveLine Y)).map (scalarUnitPullIso Λ Y).hom ≫ cP.iso.hom := by
  have h := endpoint_pull_square a (ProjectiveLine Y ↘ Y) cY cP
    (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y))
    (nativeUnitPullEndpoint Λ' (ProjectiveLine Y ↘ Y))
    (map_coefficientMap_comp_condensedPullbackHom a (ProjectiveLine Y ↘ Y))
  rw [unitPullEndpoint_eq, unitPullEndpoint_eq] at h
  coefficient_finish h

private theorem trace_eqToIso_symm
    {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm := by
  subst Y
  rfl

private theorem oppositeComparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (CondensedRing.leftDerivedUpperStarComp Λ (firstProjection Y)
        (ProjectiveLine Y ↘ Y)).symm ≪≫
      Functor.leftDerivedFunctorNatIso _
        (CondensedRing.upperStarCongr Λ
          (show firstProjection Y ≫ (ProjectiveLine Y ↘ Y) =
              secondProjection Y ≫ (ProjectiveLine Y ↘ Y) from pullback.condition)) ≪≫
      CondensedRing.leftDerivedUpperStarComp Λ (secondProjection Y)
        (ProjectiveLine Y ↘ Y) =
      (condensedAmbientPullbackComparison Λ (square Y)).symm := by
  rw [derivedCongr_eq]
  unfold condensedAmbientPullbackComparison square
  simp only [Iso.trans_symm, Iso.symm_symm_eq, trace_eqToIso_symm, Iso.trans_assoc]

private theorem firstTraceExchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N) :
    firstTraceExchange Λ Y T N e =
      (derivedExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
        (secondProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition).app T ≫
        (CondensedRing.lowerStar Λ (firstProjection Y)).rightDerivedFunctor.map e.hom := by
  have hc := congrArg Iso.hom (oppositeComparison_eq Λ Y)
  have hh := congrArg
    (fun t :
      moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (firstProjection Y) ⟶
        moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (secondProjection Y) ↦
      (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
          (ProjectiveLine Y ↘ Y))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
        (TwoSquare.mk _ _ _ _ t)).app T ≫
        (CondensedRing.lowerStar Λ (firstProjection Y)).rightDerivedFunctor.map e.hom) hc
  unfold firstTraceExchange derivedExchange
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  coefficient_finish hh.symm

private theorem trace_square_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (F' : C' ⥤ D') (T : C ⥤ C') (U : D ⥤ D')
    (α : F ⋙ U ≅ T ⋙ F')
    {K V : C} {K' V' : C'} {J W : D} {J' W' : D'}
    (c : T.obj K ⟶ K') (m : T.obj V ⟶ V') [IsIso m]
    (d : U.obj J ⟶ J') (n : U.obj W ⟶ W')
    (u : F.obj K ⟶ J) (u' : F'.obj K' ⟶ J')
    (β : F.obj V ⟶ W) (β' : F'.obj V' ⟶ W')
    (t : V ⟶ K) (t' : V' ⟶ K') (s : W ⟶ J) (s' : W' ⟶ J')
    (hc : T.map t ≫ c = m ≫ t')
    (hd : U.map s ≫ d = n ≫ s')
    (hu : α.hom.app K ≫ F'.map c ≫ u' = U.map u ≫ d)
    (hβ : α.hom.app V ≫ F'.map m ≫ β' = U.map β ≫ n)
    (h : β ≫ s = F.map t ≫ u) : β' ≫ s' = F'.map t' ≫ u' := by
  apply (cancel_epi (α.hom.app V ≫ F'.map m)).1
  calc
    (α.hom.app V ≫ F'.map m) ≫ (β' ≫ s') =
        U.map β ≫ n ≫ s' := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ s') hβ
    _ = U.map β ≫ U.map s ≫ d := by rw [← hd]
    _ = U.map (F.map t) ≫ U.map u ≫ d := by
      rw [← U.map_comp_assoc, h, U.map_comp, Category.assoc]
    _ = U.map (F.map t) ≫ α.hom.app K ≫ F'.map c ≫ u' := by rw [← hu]
    _ = α.hom.app V ≫ F'.map (T.map t) ≫ F'.map c ≫ u' := by
      simpa only [Functor.comp_map, Category.assoc] using
        α.hom.naturality_assoc t (F'.map c ≫ u')
    _ = (α.hom.app V ≫ F'.map m) ≫ (F'.map t' ≫ u') := by
      rw [← F'.map_comp_assoc, hc, F'.map_comp]
      simp only [Category.assoc]

private theorem nativeTrace_scalar
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (cL : Endpoint a M M' m)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (e : R.R = (CondensedRing.lowerStar Λ f).rightDerivedFunctor)
    (e' : R'.R = (CondensedRing.lowerStar Λ' f).rightDerivedFunctor)
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) R e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar Λ' f) R' e')
    (t : R.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧) ⟶
      unit Λ S)
    (t' : R'.R.obj (((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M') ⟦(2 : ℤ)⟧) ⟶
      unit Λ' S)
    (s : TraceCompatibility a f cU cL R R' t t') :
    (derivedScalars a S).map ((eqToIso e).inv.app _ ≫ t) ≫ cU.iso.hom =
      (derivedPushHom a f).app _ ≫
        (CondensedRing.lowerStar Λ' f).rightDerivedFunctor.map (cL.shift a) ≫
          (eqToIso e').inv.app _ ≫ t' := by
  apply (cancel_epi ((derivedScalars a S).map ((eqToIso e).hom.app _))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← (derivedScalars a S).map_comp_assoc]
  simp only [Iso.hom_inv_id_app]
  erw [(derivedScalars a S).map_id, Category.id_comp]
  have hn := normalized_push a f R R' e e' he he' s.square
    (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧)
  rw [reassoc_of% hn]
  rw [← (eqToIso e').hom.naturality_assoc (cL.shift a)]
  simp only [Iso.hom_inv_id_app_assoc]
  exact s.trace

private theorem nativeTrace_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar Λ f'))
    (e : D.R = derivedLower Λ f) (e' : D'.R = derivedLower Λ f')
    {L : Modules Λ X} {L' : Modules Λ X'}
    {m : (upperStar Ab.{u + 1} hX).obj L.X ⟶ L'.X}
    (line : PullEndpoint Λ hX L L' m) (c : UnitPullEndpoint Λ hS)
    (t : D.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ⟶
      unit Λ S)
    (t' : D'.R.obj (((DerivedCategory.singleFunctor (Modules Λ X') 0).obj L') ⟦(2 : ℤ)⟧) ⟶
      unit Λ S')
    (ht : TracePullback Λ f f' hX hS h D D' e e' line c t t') :
    (derivedExchange Λ f f' hX hS h).app _ ≫
      (derivedLower Λ f').map (nativePullEndpointShift line) ≫ (eqToIso e').inv.app _ ≫ t' =
    (derivedUpper Λ hS).map ((eqToIso e).inv.app _ ≫ t) ≫ c.derived := by
  apply (cancel_epi ((derivedUpper Λ hS).map ((eqToIso e).hom.app _))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← (derivedUpper Λ hS).map_comp_assoc]
  simp only [Iso.hom_inv_id_app]
  erw [(derivedUpper Λ hS).map_id, Category.id_comp]
  rw [(eqToIso e').inv.naturality_assoc (nativePullEndpointShift line)]
  simpa only [modelExchange, nativePullEndpointShift, Category.assoc] using ht.2.symm

section IntegralRootPullback

set_option allowUnsafeReducibility true in
attribute [local reducible] CondensedRing.lowerStar Mod.comap Mod.forget

private theorem pullEndpoint_normalization_of_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (e : (CondensedRing.upperStar Λ f).obj M ≅ N)
    (h : (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ e.hom.hom = m) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N) e.hom).hom =
      (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X m := by
  have hn :
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N) e.hom).hom =
        (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ e.hom.hom) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} f).map e.hom.hom = _
    erw [(Scheme.proEtaleSheafDirectImage f Ab.{u + 1}).map_comp, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (lowerStar Ab.{u + 1} f).map e.hom.hom)
      (moduleUnit_forget_inv Λ f M).symm
  exact hn.trans (congrArg
    ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X) h)

private theorem restrictedPullEndpoint_nonempty
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ' S) (N : Modules Λ' X)
    (c : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ' S)).obj M ⟶
      (Mod.comap (condensedPullbackHom Λ' f)).obj N) [hc : IsIso c.hom] :
    Nonempty (PullEndpoint Λ f ((Mod.comap (coefficientMap a S)).obj M)
      ((Mod.comap (coefficientMap a X)).obj N) c.hom) := by
  obtain ⟨d, hd⟩ := restrict_semilinear (upperStar Ab.{u + 1} f)
    (coefficientMap a S) (coefficientMap a X)
    (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f) M N c
  have : IsIso d.hom := hd.symm ▸ hc
  obtain ⟨e, he⟩ := ordinaryLift_iso f Λ _ _ d
  refine ⟨⟨e, ?_⟩⟩
  apply pullEndpoint_normalization_of_forget Λ f _ _ _ e
  exact he.trans hd

private theorem zlPullEndpoint_nonempty (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    Nonempty (PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X) (spIntegralComparison f l (bottomField l))) := by
  obtain ⟨c, hc⟩ := integralModuleComparison_exists f l (bottomField l)
  have : IsIso c.hom := by
    rw [hc]
    exact nativeIntegralComparison_isIso f l (bottomField l)
  have h := restrictedPullEndpoint_nonempty (integralMap l (bottomField l)) f
    (spIntegralTwist S l (bottomField l)) (spIntegralTwist X l (bottomField l)) c
  erw [hc] at h
  exact h

end IntegralRootPullback

set_option allowUnsafeReducibility true in
attribute [local reducible] CondensedRing.lowerStar Mod.comap Mod.forget in
private def cartesianPullEndpoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (hr : SpInternalCartesian f Λ M N r) : PullEndpoint Λ f M N r where
  iso := linePullIso Λ f M N r hr
  normalization := by
    exact eq_of_heq (linePull_existsUnique Λ f M N r hr).exists.choose_spec

set_option allowUnsafeReducibility true in
attribute [local reducible] CondensedRing.lowerStar Mod.comap Mod.forget in
private theorem chosenPullEndpoint_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (hr : SpInternalCartesian f Λ M N r)
    (j : (CondensedRing.upperStar Λ f).obj M ≅ N)
    (hj : j = linePullIso Λ f M N r hr) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N) j.hom).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv M.X N.X r := by
  rw [hj]
  exact eq_of_heq (linePull_existsUnique Λ f M N r hr).exists.choose_spec

private def chosenPullEndpoint_normalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (hr : SpInternalCartesian f Λ M N r)
    (j : (CondensedRing.upperStar Λ f).obj M ≅ N)
    (hj : j = linePullIso Λ f M N r hr) :
    PullEndpoint Λ f M N r where
  iso := j
  normalization := chosenPullEndpoint_normalization Λ f M N r hr j hj

set_option allowUnsafeReducibility true in
attribute [local reducible] coefficient line diagram

private def integralPullEndpoint (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E) (spIntegralComparison f l E) :=
  cartesianPullEndpoint _ f _ _ _ ((adicComparison l f).integral_rational_cartesian E).1

private def rationalPullEndpoint (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    PullEndpoint (coefficient l (some E)).X f
      (line l (some E) S) (line l (some E) X) ((adicComparison l f).rational E) :=
  chosenPullEndpoint_normalized _ f _ _ _
    ((adicComparison l f).integral_rational_cartesian E).2 (lineComparison l (some E) f) rfl

private def closurePullEndpoint (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    PullEndpoint (coefficient l none).X f
      (line l none S) (line l none X) (adicComparison l f).qbar :=
  chosenPullEndpoint_normalized _ f _ _ _ (adicComparison l f).qbar_cartesian
    (lineComparison l none f) rfl

-- Unfold only the selected coefficient and line when fixing the native endpoints.
private def nativeRationalEndpoint (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    PullEndpoint (Profinite.continuousMapRingObj.{u} E.1) f
      (spRationalTwist S l E) (spRationalTwist X l E)
      ((adicComparison l f).rational E) := by
  have e := rationalPullEndpoint l E f
  unfold coefficient line at e
  exact e

-- Unfold only the selected coefficient and line when fixing the native endpoints.
private def nativeClosureEndpoint (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    PullEndpoint (Profinite.padicAlgClRingObj.{u} l) f
      (spQbarTwist S l) (spQbarTwist X l) (adicComparison l f).qbar := by
  have e := closurePullEndpoint l f
  unfold coefficient line at e
  exact e

attribute [local irreducible] linePullIso adicComparison lineComparison shiftedLineComparison

private theorem endpointShift_iso_formula
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m) :
    nativePullEndpointShift e =
      (((moduleObjectDerivedPullback Λ f).commShiftIso (2 : ℤ)).app
        ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso
          (((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.app M) ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso e.iso)).hom := by
  rw [nativePullEndpointShift_formula]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  rfl

private theorem rationalPullEndpoint_shift (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    nativePullEndpointShift (rationalPullEndpoint l E f) =
      (shiftedLineComparison l (some E) f).hom := by
  have h := endpointShift_iso_formula (rationalPullEndpoint l E f)
  unfold shiftedLineComparison
  exact h

private theorem closurePullEndpoint_shift (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    nativePullEndpointShift (closurePullEndpoint l f) = (shiftedLineComparison l none f).hom := by
  have h := endpointShift_iso_formula (closurePullEndpoint l f)
  unfold shiftedLineComparison
  exact h

set_option allowUnsafeReducibility true in
attribute [local irreducible] coefficient

private def oppositeSquare (Y : Scheme.{u}) :
    ChosenCartesianSquare (secondProjection Y) (firstProjection Y)
      (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) where
  w := pullback.condition.symm
  isoPullback := pullbackSymmetry _ _
  hom_fst := pullbackSymmetry_hom_comp_fst _ _
  hom_snd := pullbackSymmetry_hom_comp_snd _ _

private theorem oppositeExchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    derivedExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
        (secondProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition =
      condensedAmbientExchange Λ (oppositeSquare Y) := by
  have hc :
      (CondensedRing.leftDerivedUpperStarComp Λ (firstProjection Y)
          (ProjectiveLine Y ↘ Y)).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          (CondensedRing.upperStarCongr Λ
            (show firstProjection Y ≫ (ProjectiveLine Y ↘ Y) =
                secondProjection Y ≫ (ProjectiveLine Y ↘ Y) from pullback.condition)) ≪≫
        CondensedRing.leftDerivedUpperStarComp Λ (secondProjection Y)
          (ProjectiveLine Y ↘ Y) =
        condensedAmbientPullbackComparison Λ (oppositeSquare Y) := by
    rw [derivedCongr_eq]
    unfold condensedAmbientPullbackComparison oppositeSquare
    rfl
  have hh := congrArg
    (fun t :
      moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (firstProjection Y) ⟶
        moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (secondProjection Y) ↦
      (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
          (ProjectiveLine Y ↘ Y))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
        (TwoSquare.mk _ _ _ _ t))) (congrArg Iso.hom hc)
  unfold derivedExchange condensedAmbientExchange
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  coefficient_finish hh

private def NativeTraceSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) : Prop :=
  (condensedAmbientExchange Λ (oppositeSquare Y)).app _ ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e ≫
        (eqToIso d.p₁_canonical).inv.app _ ≫ d.trace₁ =
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      ((eqToIso d.q_canonical).inv.app _ ≫ d.traceq) ≫ (scalarUnitPullIso Λ Y).hom

attribute [local irreducible] derivedPullIso derivedPushHom

-- Paste normalized squares while keeping the coefficient category instances folded.
private theorem nativeTraceSquare_scalar
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X)
    (d : Diagram Λ Y L) (d' : Diagram Λ' Y L')
    (s : ScalarCompatibility a Y L L' m d d')
    {r : (upperStar Ab.{u + 1} (secondProjection Y)).obj
      (L (ProjectiveLine Y)).X ⟶ (L (diagonalSurface Y)).X}
    {r' : (upperStar Ab.{u + 1} (secondProjection Y)).obj
      (L' (ProjectiveLine Y)).X ⟶ (L' (diagonalSurface Y)).X}
    (e : PullEndpoint Λ (secondProjection Y) (L (ProjectiveLine Y))
      (L (diagonalSurface Y)) r)
    (e' : PullEndpoint Λ' (secondProjection Y) (L' (ProjectiveLine Y))
      (L' (diagonalSurface Y)) r')
    (hr : (upperStar Ab.{u + 1} (secondProjection Y)).map (m (ProjectiveLine Y)) ≫ r' =
      r ≫ m (diagonalSurface Y))
    (h : NativeTraceSquare Λ Y L d (nativePullEndpointShift e)) :
    NativeTraceSquare Λ' Y L' d' (nativePullEndpointShift e') := by
  let V := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  let b := (derivedPushHom a (ProjectiveLine Y ↘ Y)).app V ≫
    (moduleObjectDerivedPushforward Λ' (ProjectiveLine Y ↘ Y)).map (s.lineP.shift a)
  have hb : IsIso b := by
    have hp := normalized_push a (ProjectiveLine Y ↘ Y) d.Rq d'.Rq
      d.q_canonical d'.q_canonical d.q_unit d'.q_unit s.q.square V
    have : IsIso ((s.q.square.mate a).app V) := s.q.comparison_iso
    have : IsIso ((derivedPushHom a (ProjectiveLine Y ↘ Y)).app V) := by
      apply IsIso.of_isIso_fac_left hp
    dsimp only [b]
    unfold Endpoint.shift
    infer_instance
  have hq := nativeTrace_scalar a (ProjectiveLine Y ↘ Y)
    (s.units Y) s.lineP d.Rq d'.Rq d.q_canonical d'.q_canonical
    d.q_unit d'.q_unit d.traceq d'.traceq s.q
  have hp := nativeTrace_scalar a (firstProjection Y)
    (s.units (ProjectiveLine Y)) s.lineW d.R₁ d'.R₁ d.p₁_canonical d'.p₁_canonical
    d.p₁_unit d'.p₁_unit d.trace₁ d'.trace₁ s.p₁
  have hu := unit_pull_scalar a Y (s.units Y)
    (s.units (ProjectiveLine Y))
  have he := endpoint_pull_square_shift a (secondProjection Y) s.lineP s.lineW e e' hr
  have hx := coefficient_exchange_line
    (condensedAmbientExchange Λ (oppositeSquare Y))
    (condensedAmbientExchange Λ' (oppositeSquare Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y))
    (derivedPullIso a (secondProjection Y)).hom
    (derivedPushHom a (ProjectiveLine Y ↘ Y)) (derivedPushHom a (firstProjection Y))
    (s.lineP.shift a) (nativePullEndpointShift e) (nativePullEndpointShift e') (s.lineW.shift a)
    (flat_coefficient_exchange a (oppositeSquare Y) V) he
  have hh := trace_square_transport
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y))
    (derivedScalars a Y) (derivedScalars a (ProjectiveLine Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y))
    (s.units Y).iso.hom b (s.units (ProjectiveLine Y)).iso.hom
    ((derivedPushHom a (firstProjection Y)).app _ ≫
      (moduleObjectDerivedPushforward Λ' (firstProjection Y)).map (s.lineW.shift a))
    (scalarUnitPullIso Λ Y).hom (scalarUnitPullIso Λ' Y).hom
    _ _ _ _ _ _
    (by simpa only [b, Category.assoc] using hq)
    (by simpa only [Category.assoc] using hp) hu hx
    (by
      have h₀ := h
      dsimp only [NativeTraceSquare] at h₀
      simp only [Category.assoc] at h₀ ⊢
      coefficient_finish h₀)
  unfold NativeTraceSquare
  simp only [Category.assoc] at hh ⊢
  coefficient_finish hh

-- Compose equalities of the two boundaries without dependent rewriting of the square.
private theorem nativeTraceSquare_of_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    {r : (upperStar Ab.{u + 1} (secondProjection Y)).obj
      (L (ProjectiveLine Y)).X ⟶ (L (diagonalSurface Y)).X}
    (e : PullEndpoint Λ (secondProjection Y) (L (ProjectiveLine Y))
      (L (diagonalSurface Y)) r)
    (h : TracePullback Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
      (secondProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition
      d.Rq d.R₁ d.q_canonical d.p₁_canonical e
      (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)) d.traceq d.trace₁) :
    NativeTraceSquare Λ Y L d (nativePullEndpointShift e) := by
  have hh := nativeTrace_pullback Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition
    d.Rq d.R₁ d.q_canonical d.p₁_canonical e
    (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)) d.traceq d.trace₁ h
  have hu := unitPullEndpoint_eq Λ Y
    (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y))
  unfold NativeTraceSquare
  rw [← oppositeExchange_eq]
  have h' := hh.trans (congrArg
    (fun t ↦ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      ((eqToIso d.q_canonical).inv.app _ ≫ d.traceq) ≫ t) hu)
  coefficient_finish h'

private theorem nativeTraceSquare_to_first
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (h : NativeTraceSquare Λ Y L d e.hom) :
    firstTraceExchange Λ Y _ _ e ≫
      firstNativeFunctional Λ Y L d _ d.trace₁ ≫
        (singleUnitIso Λ (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
        (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫
          (secondTraceUnitIso Λ Y).hom := by
  have ht' := congrArg
    (fun z ↦ z ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom) h
  rw [firstTraceExchange_eq, oppositeExchange_eq]
  simp only [firstNativeFunctional, trace, scalarUnitPullIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, id_eq] at ht' ⊢
  coefficient_finish ht'

-- Assemble the integral, rational, and closure squares in their fixed coefficient types.
private theorem native_scalar_trace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤))) :
    NativeTraceSquare (coefficient l c).X Y (line l c) (diagram l c Y family)
      (shiftedLineComparison l c (secondProjection Y)).hom := by
  obtain ⟨line₀⟩ := zlPullEndpoint_nonempty l (secondProjection Y)
  let c₀ : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (ProjectiveLine Y ↘ Y) :=
    nativeUnitPullEndpoint _ _
  have hz := tracePullback_of_realized l
    (ProjectiveLine Y ↘ Y) (firstProjection Y) (secondProjection Y)
    (ProjectiveLine Y ↘ Y)
    (by simpa only [firstProjection, secondProjection] using
      (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).flip)
    hY hP reference.eP reference.eY reference.eW reference.eP reference.tq reference.t₁
    family.zl.Rq family.zl.R₁ family.zl.q_canonical family.zl.p₁_canonical
    family.zl.q_unit family.zl.p₁_unit reference.q_square reference.p₁_square line₀ c₀
    _ _ reference.q_trace reference.p₁_trace
  have hzl := nativeTraceSquare_of_pullback _ Y (zlLine l) family.zl line₀ hz
  have hi (E : PadicAlgCl.FiniteIntermediateField l) :
      NativeTraceSquare (Profinite.padicIntegersRingObj.{u} l E.1) Y
        (fun X ↦ spIntegralTwist X l E) (family.integral E)
        (nativePullEndpointShift (integralPullEndpoint l E (secondProjection Y))) := by
    have : ∀ S : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (integralMap l E) S)) :=
      (integralScalarComparison_isIso l E (ProjectiveLine Y ↘ Y)).choose
    apply nativeTraceSquare_scalar (integralMap l E) Y _ _ _ _ _
      (family.toIntegral E) line₀ (integralPullEndpoint l E (secondProjection Y)) _ hzl
    exact (adicComparison l (secondProjection Y)).integral_inclusion
      (bottomField l) E (by
        change (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1
        exact bot_le)
  have hr (E : PadicAlgCl.FiniteIntermediateField l) :
      NativeTraceSquare (Profinite.continuousMapRingObj.{u} E.1) Y
        (fun X ↦ spRationalTwist X l E) (family.rational E)
        (nativePullEndpointShift (nativeRationalEndpoint l E (secondProjection Y))) := by
    have : ∀ S : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) S)) :=
      fun S ↦ preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield l E S
    exact nativeTraceSquare_scalar (padicIntegersRingObjToContinuousMapRingObj l E) Y
      _ _ _ _ _ (family.toRational E) (integralPullEndpoint l E (secondProjection Y))
      (nativeRationalEndpoint l E (secondProjection Y))
      (rational_root_scalar_square l E (secondProjection Y)) (hi E)
  have hc : NativeTraceSquare (Profinite.padicAlgClRingObj.{u} l) Y
      (fun X ↦ spQbarTwist X l) family.closure
      (nativePullEndpointShift (nativeClosureEndpoint l (secondProjection Y))) := by
    have : ∀ S : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l (bottomField l)) S)) :=
      fun S ↦ CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
        l S (bottomField l)
    exact nativeTraceSquare_scalar (Profinite.padicSubfieldRingObjToPadicAlgCl l
      (bottomField l)) Y _ _ _ _ _ (family.toClosure (bottomField l))
      (nativeRationalEndpoint l (bottomField l) (secondProjection Y))
      (nativeClosureEndpoint l (secondProjection Y))
      ((adicComparison l (secondProjection Y)).qbar_coprojection (bottomField l))
      (hr (bottomField l))
  have ht : NativeTraceSquare (coefficient l c).X Y (line l c) (diagram l c Y family)
      (shiftedLineComparison l c (secondProjection Y)).hom := by
    cases c with
    | some E =>
      have h := hr E
      have hs := rationalPullEndpoint_shift l E (secondProjection Y)
      unfold nativeRationalEndpoint at h
      unfold coefficient line at hs
      unfold coefficient line diagram
      rw [← hs]
      exact h
    | none =>
      have hs := closurePullEndpoint_shift l (secondProjection Y)
      unfold nativeClosureEndpoint at hc
      unfold coefficient line at hs
      unfold coefficient line diagram
      rw [← hs]
      exact hc
  exact ht

-- Assemble the completed square and the three concrete scalar transports.
/-- Base change of the normalized q trace to the first projection. -/
theorem first_scalar_trace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family) :
    firstTraceExchange (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (secondLineComparison l c k p hpl Y) ≫
      firstNativeFunctional (coefficient l c).X Y (line l c) (diagram l c Y family)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (diagram l c Y family).trace₁ ≫
      (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (trace (coefficient l c).X Y (line l c) (diagram l c Y family) ≫
        (singleUnitIso (coefficient l c).X Y).hom) ≫
      (secondTraceUnitIso (coefficient l c).X Y).hom := by
  let : ∀ x : Y, Invertible (l : Y.residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _ (Y ↘ Spec (.of k)) x).invertible
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  apply nativeTraceSquare_to_first _ Y _ _ (secondLineComparison l c k p hpl Y)
  unfold secondLineComparison
  exact native_scalar_trace l c Y δ family reference hY hP

end AlgebraicGeometry.ProEtale.RationalP1
