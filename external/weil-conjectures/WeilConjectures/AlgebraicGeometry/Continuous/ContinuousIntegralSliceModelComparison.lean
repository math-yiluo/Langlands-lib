/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeCoefficientPullbackIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Integral scalar models on a slice site

Source: Bhatt--Scholze, Lemma 6.5.8(1) and Definition 6.8.10.
(blueprint: lem-weil-pbc-continuous-integral-slice-model-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

namespace ContinuousIntegralSlice
open Scheme

private abbrev modules (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((adicLisseForget X).obj R)

private abbrev tensor {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u} a

-- The following constant/global-sections adjunction calculation follows the proved
-- private calculation in FiniteFreeConstructibleScalarTransport. Keeping it here
-- avoids importing that file's unrelated derived constructibility dependencies.
private def constantPF (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((constantPF X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

private def constantPFAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    constantPF X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private def constantGlobal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

private def constantAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ constantGlobal X A T :=
  (constantPFAdj X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit X A))

private def integralGlobal {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (pbcCompletedScalar X d) ⋙ constantGlobal X A T

private def integralAdj {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobal X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

private def realization (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :=
  adicLisseConstantModules X (ULift.{u + 1} A) ⋙
    tensor (continuousCoefficientConstantMap X A)

private def realizationGlobal (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] (V : X.ProEt) :=
  pbcRestrict (continuousCoefficientConstantMap X A) ⋙
    constantGlobal X (ULift.{u + 1} A) V

private def realizationAdj (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (V : X.ProEt) (hV : IsTerminal V) :
    realization X A ⊣ realizationGlobal X A V :=
  (constantAdj X (ULift.{u + 1} A) V hV).comp
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u}
      (continuousCoefficientConstantMap X A))

private def pull {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :=
  proEtaleModuleInverseImage h (latticeCoefficientSheaf X A) ⋙
    tensor (continuousCoefficientInverseImageMap h A)

private def pullAdj {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    pull h A ⊣ pbcRestrict (continuousCoefficientInverseImageMap h A) ⋙
      T h (latticeCoefficientSheaf X A) :=
  (canonicalAdjunction h (latticeCoefficientSheaf X A)).comp
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u}
      (continuousCoefficientInverseImageMap h A))

private def transport (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (e : R ≅ S) :
    modules X S ≌ modules X R :=
  CondensedRing.ringModuleEquivalenceOfIso X ((adicLisseForget X).mapIso e)

private def coefficientIso {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : B ≅ latticeCoefficientSheaf X A)
    [IsIso (continuousCoefficientInverseImageMap h A)] :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ≅
      latticeCoefficientSheaf Z A :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c ≪≫
    asIso (continuousCoefficientInverseImageMap h A)

private theorem coefficientAdjunct {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : B ≅ latticeCoefficientSheaf X A)
    [IsIso (continuousCoefficientInverseImageMap h A)] :
    (proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
          (coefficientIso h A c).hom =
      c.hom ≫ continuousCoefficientDirectImageMap h A := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  change adj.homEquiv _ _
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map c.hom ≫
      continuousCoefficientInverseImageMap h A) = _
  rw [adj.homEquiv_naturality_left]
  unfold continuousCoefficientInverseImageMap
  rw [Equiv.apply_symm_apply]

private def pullRightIso {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : B ≅ latticeCoefficientSheaf X A)
    [IsIso (continuousCoefficientInverseImageMap h A)] :
    (transport Z (coefficientIso h A c).symm).inverse ⋙ T h B ⋙
        (transport X c).inverse ≅
      pbcRestrict (continuousCoefficientInverseImageMap h A) ⋙
        T h (latticeCoefficientSheaf X A) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro a
      ext n
      symm
      have hq := congrArg (fun k ↦ k.hom.app W a)
        (Equiv.apply_symm_apply
          ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv
            (latticeCoefficientSheaf X A) (latticeCoefficientSheaf Z A))
          (continuousCoefficientDirectImageMap h A))
      have he : c.hom.hom.app W (c.inv.hom.app W a) = a :=
        congrArg (fun k ↦ k.hom.app W a) c.inv_hom_id
      change AddCommGrpCat.Hom.hom ((N.val.obj ((proEtaleBaseChange h).op.obj W)).smul
          ((coefficientIso h A c).hom.hom.app ((proEtaleBaseChange h).op.obj W)
            (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app W
              (c.inv.hom.app W a)))).asHom n =
        AddCommGrpCat.Hom.hom ((N.val.obj ((proEtaleBaseChange h).op.obj W)).smul
          ((continuousCoefficientInverseImageMap h A).hom.app
            ((proEtaleBaseChange h).op.obj W)
              (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
                (latticeCoefficientSheaf X A)).hom.app W a))).asHom n
      have hc' := congrArg (fun k ↦ k.hom.app W (c.inv.hom.app W a))
        (coefficientAdjunct h A c)
      change (coefficientIso h A c).hom.hom.app ((proEtaleBaseChange h).op.obj W)
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app W
          (c.inv.hom.app W a)) =
        (continuousCoefficientDirectImageMap h A).hom.app W
          (c.hom.hom.app W (c.inv.hom.app W a)) at hc'
      rw [he] at hc'
      rw [hc']
      exact congrArg
        (fun r ↦ AddCommGrpCat.Hom.hom
          ((N.val.obj ((proEtaleBaseChange h).op.obj W)).smul r).asHom n) hq.symm
    · intro W W' f
      ext n
      rfl
  · intro N N' f
    ext W n
    rfl

private def pullIso {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : B ≅ latticeCoefficientSheaf X A)
    [IsIso (continuousCoefficientInverseImageMap h A)] :
    (transport X c).functor ⋙ proEtaleModuleInverseImage h B ⋙
        (transport Z (coefficientIso h A c).symm).functor ≅ pull h A :=
  ((((transport X c).toAdjunction.comp (canonicalAdjunction h B)).comp
    (transport Z (coefficientIso h A c).symm).toAdjunction).ofNatIsoRight
      (pullRightIso h A c)).leftAdjointUniq (pullAdj h A)

private theorem constants_unit (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (W : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (continuousCoefficientConstantMap X A).hom.app W
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W a) =
      (continuousCoefficientConstants X A).app W a := by
  have he := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
      (latticeCoefficientSheaf X A)) (continuousCoefficientConstants X A)
  exact congrArg (fun k ↦ k.app W a) he

private theorem normalizedSections (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {O : Type (u + 1)} [CommRing O] (d : AdicCoefficientDatum O)
    (s : ULift.{u + 1} A ≃+* O)
    (c : pbcAdicCompletion X d ≅ latticeCoefficientSheaf X A)
    (hc : (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        s.toCommRingCatIso.hom ≫ pbcCompletedScalar X d =
      continuousCoefficientConstantMap X A ≫ c.inv)
    (W : X.ProEtᵒᵖ) (a : O) :
    c.hom.hom.app W (pbcCompletedSection X d W a) =
      (continuousCoefficientConstants X A).app W (s.symm a) := by
  let J := ProEt.topology X
  let τ := toSheafify J
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
  have hu := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map s.toCommRingCatIso.hom)) W) (s.symm a)
  change (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of O))).app W
      (s (s.symm a)) =
    ((constantSheaf J CommRingCat.{u + 1}).map s.toCommRingCatIso.hom).hom.app W
      (τ.app W (s.symm a)) at hu
  rw [s.apply_symm_apply] at hu
  have hh := congrArg (fun k ↦ k.hom.app W (τ.app W (s.symm a))) hc
  change (pbcCompletedScalar X d).hom.app W
      (((constantSheaf J CommRingCat.{u + 1}).map s.toCommRingCatIso.hom).hom.app W
        (τ.app W (s.symm a))) =
    c.inv.hom.app W ((continuousCoefficientConstantMap X A).hom.app W
      (τ.app W (s.symm a))) at hh
  rw [← hu, constants_unit] at hh
  change pbcCompletedSection X d W a = _ at hh
  rw [hh]
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app W) c.inv_hom_id) _

private def modelRightIso {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {O : Type (u + 1)} [CommRing O] (d : AdicCoefficientDatum O)
    (s : ULift.{u + 1} A ≃+* O)
    (c : pbcAdicCompletion X d ≅ latticeCoefficientSheaf X A)
    (hc : (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        s.toCommRingCatIso.hom ≫ pbcCompletedScalar X d =
      continuousCoefficientConstantMap X A ≫ c.inv)
    [IsIso (continuousCoefficientInverseImageMap h A)] (V : X.ProEt) :
    (transport Z (coefficientIso h A c).symm).inverse ⋙
        T h (pbcAdicCompletion X d) ⋙ integralGlobal X d V ≅
      realizationGlobal Z A ((proEtaleBaseChange h).obj V) ⋙
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv s).inverse := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro a
    ext n
    symm
    have hh := congrArg (fun k ↦ k.hom.app (op V) (pbcCompletedSection X d (op V) a))
      (coefficientAdjunct h A c)
    change (coefficientIso h A c).hom.hom.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
          (pbcAdicCompletion X d)).hom.app (op V) (pbcCompletedSection X d (op V) a)) =
      (continuousCoefficientDirectImageMap h A).hom.app (op V)
        (c.hom.hom.app (op V) (pbcCompletedSection X d (op V) a)) at hh
    rw [normalizedSections X A d s c hc] at hh
    change AddCommGrpCat.Hom.hom ((N.val.obj (op ((proEtaleBaseChange h).obj V))).smul
        ((coefficientIso h A c).hom.hom.app (op ((proEtaleBaseChange h).obj V))
          (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
            (pbcAdicCompletion X d)).hom.app (op V)
              (pbcCompletedSection X d (op V) a)))).asHom n =
      AddCommGrpCat.Hom.hom ((N.val.obj (op ((proEtaleBaseChange h).obj V))).smul
        ((continuousCoefficientConstantMap Z A).hom.app
          (op ((proEtaleBaseChange h).obj V))
            ((toSheafify (ProEt.topology Z)
              ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
                (op ((proEtaleBaseChange h).obj V)) (s.symm a)))).asHom n
    rw [hh, constants_unit]
    rfl
  · intro N N' f
    ext n
    rfl

private def modelIso {X Z : Scheme.{u}} (h : Z ⟶ X) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {O : Type (u + 1)} [CommRing O] (d : AdicCoefficientDatum O)
    (s : ULift.{u + 1} A ≃+* O)
    (c : pbcAdicCompletion X d ≅ latticeCoefficientSheaf X A)
    (hc : (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        s.toCommRingCatIso.hom ≫ pbcCompletedScalar X d =
      continuousCoefficientConstantMap X A ≫ c.inv)
    [IsIso (continuousCoefficientInverseImageMap h A)] :
    integralConstantModule X d ⋙ proEtaleModuleInverseImage h (pbcAdicCompletion X d) ⋙
        (transport Z (coefficientIso h A c).symm).functor ≅
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv s).functor ⋙ realization Z A := by
  let V := ⊤_ X.ProEt
  let hV := terminalIsTerminal (C := X.ProEt)
  exact ((((integralAdj X d V hV).comp
    (canonicalAdjunction h (pbcAdicCompletion X d))).comp
      (transport Z (coefficientIso h A c).symm).toAdjunction).ofNatIsoRight
        (modelRightIso h A d s c hc V)).leftAdjointUniq
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv s).toAdjunction.comp
            (realizationAdj Z A ((proEtaleBaseChange h).obj V)
              (hV.isTerminalObj (proEtaleBaseChange h))))

private def overTransport (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (e : R ≅ S) (U : X.ProEt) :
    SheafOfModules.{u + 1} (((adicLisseForget X).obj S).over U) ≌
      SheafOfModules.{u + 1} (((adicLisseForget X).obj R).over U) := by
  let k := ((ProEt.topology X).overPullback RingCat.{u + 1} U).mapIso
    ((adicLisseForget X).mapIso e)
  let eqv : Over U ≌ Over U :=
    ⟨𝟭 _, 𝟭 _, Iso.refl _, Iso.refl _, fun _ ↦ Category.id_comp _⟩
  letI : eqv.functor.IsContinuous ((ProEt.topology X).over U)
      ((ProEt.topology X).over U) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  letI : eqv.inverse.IsContinuous ((ProEt.topology X).over U)
      ((ProEt.topology X).over U) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  exact SheafOfModules.pushforwardPushforwardEquivalence eqv k.hom k.inv
    (by ext W : 2
        exact (((adicLisseForget X).obj S).over U).obj.map_id W |>.trans
          (congr_app (congrArg (fun f ↦ f.hom) k.inv_hom_id) W).symm)
    (by ext W : 2
        exact (congrArg (fun f ↦ k.hom.hom.app W ≫ k.inv.hom.app W ≫ f)
          ((((adicLisseForget X).obj R).over U).obj.map_id W)).trans
            ((Category.comp_id _).trans
              (congr_app (congrArg (fun f ↦ f.hom) k.hom_inv_id) W)))

private theorem finitePresentation_restrict
    {A O : Type (u + 1)} [CommRing A] [CommRing O] (e : A ≃+* O)
    (N : ModuleCat.{u + 1} O) [Module.FinitePresentation O N] :
    Module.FinitePresentation A ((ModuleCat.restrictScalars e.toRingHom).obj N) := by
  let : Algebra A O := e.toRingHom.toAlgebra
  let P := (ModuleCat.restrictScalars e.toRingHom).obj N
  let : Module O P := N.isModule
  have : Module.FinitePresentation O P := inferInstanceAs (Module.FinitePresentation O N)
  have : IsScalarTower A O P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e' : A ≃ₗ[A] O :=
    { e with map_smul' := fun a b ↦ by change e (a * b) = e a * e b; exact e.map_mul a b }
  have : Module.FinitePresentation A O := Module.FinitePresentation.of_equiv e'
  exact Module.FinitePresentation.trans A P O

end ContinuousIntegralSlice

/-- Coefficient transport identifies the finite scalar models on each slice after a
locally closed immersion. Both sides use ordinary scalar extension, with torsion allowed.
Source: Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.8.10 and the completed coefficient
presentation of Definition 6.5.1.
(blueprint: lem-weil-pbc-continuous-integral-slice-model-comparison).

Proof: use the given normalized coefficient isomorphism c.
For a locally closed immersion h, inverse image commutes with the finite-quotient
inverse limit by Lemma 6.5.8(1). The resulting coefficient comparison is the adjunct of
precomposition of continuous functions: after every finite projection this is the
constant-ring pullback comparison. The same computation on constant sections shows
that the two scalar maps agree. Thus ordinary inverse image and scalar extension,
transported through these ring isomorphisms, commute by their adjunction universal
properties. The resulting isomorphism sends the pullback of integralConstantModule X N
to continuousCoefficientModule Z P, with P and N related by the lifted valuation-ring
isomorphism s. This is an equivalence of scalar-module categories and preserves finite
presentation. All the functor comparisons restrict to slice sites via overFunctor;
the coefficient isomorphisms induce equivalences there. Applying these equivalences
and their fully faithful inverses to the local model isomorphisms proves both directions.
The argument includes zero modules, torsion modules, the empty base and the empty slice;
it asserts no completeness for an arbitrary M. -/
theorem continuousIntegralSliceModelComparison
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [IsNoetherian X]
    (s : ULift.{u + 1} (latticeCoefficientIntegers l E) ≃+* Scheme.PbcIntegralRing l E)
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (latticeCoefficientIntegers l E))
    (_hc : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        s.toCommRingCatIso.hom ≫ Scheme.pbcCompletedScalar X (Scheme.pbcIntegralDatum l E) =
      continuousCoefficientConstantMap X (latticeCoefficientIntegers l E) ≫ c.inv) :
      ∀ {Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h]
        (M : SheafOfModules.{u + 1}
          (latticeModuleRing X (latticeCoefficientIntegers l E))) (U : Z.ProEt),
        (∃ P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)),
          Module.FinitePresentation (ULift.{u + 1} (latticeCoefficientIntegers l E)) P ∧
          Nonempty ((continuousModulePullback h (latticeCoefficientIntegers l E) M).over U ≅
            (continuousCoefficientModule Z (latticeCoefficientIntegers l E) P).over U)) ↔
        (∃ N : ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E),
          Module.FinitePresentation (Scheme.PbcIntegralRing l E) N ∧
          Nonempty ((SheafOfModules.overFunctor _ U).obj
            ((Scheme.proEtaleModuleInverseImage h
              (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                ((CondensedRing.ringModuleEquivalenceOfIso X
                  ((Scheme.adicLisseForget X).mapIso c)).functor.obj M)) ≅
            (SheafOfModules.overFunctor _ U).obj
              ((Scheme.proEtaleModuleInverseImage h
                (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                  ((Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj N)))) := by
  classical
  intro Z h _ M U
  let A := latticeCoefficientIntegers l E
  let d := Scheme.pbcIntegralDatum l E
  let B := Scheme.pbcAdicCompletion X d
  have : IsIso (continuousCoefficientInverseImageMap h A) :=
    (latticeCoefficientPullback_isIso l E h).1
  let e := ContinuousIntegralSlice.coefficientIso h A c
  let Q := ModuleCat.restrictScalarsEquivalenceOfRingEquiv s
  let H := ContinuousIntegralSlice.overTransport Z e.symm U
  let F := Scheme.proEtaleModuleInverseImage h B
  let L := (ContinuousIntegralSlice.transport X c).functor.obj M
  have hpull : H.functor.obj ((F.obj L).over U) ≅
      (continuousModulePullback h A M).over U :=
    (SheafOfModules.overFunctor _ U).mapIso
      ((ContinuousIntegralSlice.pullIso h A c).app M)
  have hmodel (N : ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E)) :
      H.functor.obj ((F.obj ((Scheme.integralConstantModule X d).obj N)).over U) ≅
        (continuousCoefficientModule Z A (Q.functor.obj N)).over U :=
    (SheafOfModules.overFunctor _ U).mapIso
      ((ContinuousIntegralSlice.modelIso h A d s c _hc).app N)
  constructor
  · rintro ⟨P, hP, ⟨a⟩⟩
    let N := Q.inverse.obj P
    have : Module.FinitePresentation (ULift.{u + 1} A) P := hP
    have hN : Module.FinitePresentation (Scheme.PbcIntegralRing l E) N :=
      ContinuousIntegralSlice.finitePresentation_restrict s.symm P
    refine ⟨N, hN, ⟨H.fullyFaithfulFunctor.preimageIso ?_⟩⟩
    exact hpull ≪≫ a ≪≫
      ((SheafOfModules.overFunctor _ U).mapIso
        ((ContinuousIntegralSlice.realization Z A).mapIso (Q.counitIso.app P))).symm ≪≫
      (hmodel N).symm
  · rintro ⟨N, hN, ⟨a⟩⟩
    have : Module.FinitePresentation (Scheme.PbcIntegralRing l E) N := hN
    refine ⟨Q.functor.obj N, ContinuousIntegralSlice.finitePresentation_restrict s N,
      ⟨hpull.symm ≪≫ H.functor.mapIso a ≪≫ hmodel N⟩⟩

end AlgebraicGeometry.ProEtale
