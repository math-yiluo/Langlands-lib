/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.RationalStratum.RationalStratumFiniteFreeModel
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.Algebra.Homology.SixFunctors.LocallyFreeDerivedScalars
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import all WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed

/-! # Ordinary rational module models under coefficient transport

The completed presentation is compared with the continuous coefficient presentation.

## References

* Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.10 and Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def extendComp {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend (a ≫ b) :=
  (((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).ofNatIsoRight
    (pbcRestrictComp a b (a ≫ b) rfl)).leftAdjointUniq (pbcScalarAdjunction (a ≫ b))

private def extendIso {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ≅ S) :
    pbcExtend c.hom ≅ pbcRestrict c.inv :=
  (pbcScalarAdjunction c.hom).leftAdjointUniq
    (AlgebraicGeometry.ProEtale.restrictionEquivalence
      ((adicLisseForget X).mapIso c).symm).toAdjunction

private def integralConstantComparison (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    integralConstantModule X d ≅ adicLisseConstantModules X A ⋙
      pbcExtend (pbcCompletedScalar X d) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let K := adicLisseConstantModules X A
  let a := adicDatumScalar X dd
  let c := pbcCompletedComparison X d
  change (K ⋙ pbcExtend a) ⋙ pbcRestrict c.inv ≅ K ⋙ pbcExtend (a ≫ c.hom)
  exact Functor.isoWhiskerLeft (K ⋙ pbcExtend a) (extendIso c).symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft K (extendComp a c.hom)

private def directConstantComparison (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E)))
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) :
    (pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj
      ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
      AlgebraicGeometry.ProEtale.RationalStratum.directModel l E X N := by
  let a := pbcCompletedScalar X (pbcIntegralDatum l E)
  let b := i.hom ≫ integralRationalCoefficientMap l E X
  let K := (adicLisseConstantModules X (PbcIntegralRing l E)).obj N
  have hab : a ≫ b = AlgebraicGeometry.ProEtale.RationalStratum.integralConstants l E X ≫
      integralRationalCoefficientMap l E X := by
    rw [← Category.assoc, hi]
    rfl
  exact (pbcExtend b).mapIso
      ((integralConstantComparison X (pbcIntegralDatum l E)).app N) ≪≫
    (extendComp a b).app K ≪≫
    eqToIso (congrArg (fun t ↦ (pbcExtend t).obj K) hab) ≪≫
    eqToIso (reductionChange_obj_eq X _ K) ≪≫
    (PurScalar.tensorFunctor.{u + 1, u + 1, u} _).mapIso
      (AlgebraicGeometry.ProEtale.RationalStratum.constantComparison X _ N)

private def rationalConstantComparison (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E)))
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (hN : Module.FinitePresentation (PbcIntegralRing l E) N) :
    (pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj
      ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
    (adicLisseConstantModules X (ULift.{u + 1} E) ⋙
      pbcExtend (letI := coefficientExtensionNormedField l E
        continuousCoefficientConstantComparison X (ULift.{u + 1} E))).obj
        ((ModuleCat.extendScalars
          (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)).obj N) := by
  let V := AlgebraicGeometry.ProEtale.RationalStratum.vectorSpace l E N
  let c := AlgebraicGeometry.ProEtale.RationalStratum.rationalConstants l E X
  let e := (AlgebraicGeometry.ProEtale.RationalStratum.scalarModels l E X).choose
  exact directConstantComparison l E X i hi N ≪≫ e N hN ≪≫
    (PurScalar.tensorFunctor.{u + 1, u + 1, u} c).mapIso
      (AlgebraicGeometry.ProEtale.RationalStratum.constantComparison X _ V).symm ≪≫
    (eqToIso (reductionChange_obj_eq X c _)).symm

private def regularInverseIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage f R).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients R)) ≅
      SheafOfModules.unit
        (proEtaleModuleCoefficients
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) := by
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Z.ProEt ⥤ proEtaleSiteModel Z).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange f).Final := inferInstance
  let : (proEtaleModelBaseChange f).IsContinuous
      (proEtaleModelTopology X) (proEtaleModelTopology Z) :=
    proEtaleModelBaseChange_isContinuous f
  have : HasWeakSheafify (proEtaleModelTopology Z) AddCommGrpCat.{u + 1} := by
    infer_instance
  have : (proEtaleModelTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
    infer_instance
  have : (PresheafOfModules.pushforward.{u + 1}
      (F := proEtaleModelBaseChange f) (proEtaleModelRingUnit f R).hom).IsRightAdjoint := by
    exact Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top
        (F := proEtaleModelBaseChange f) (proEtaleModelRingUnit f R).hom)
  have : (SheafOfModules.pushforward.{u + 1}
      (F := proEtaleModelBaseChange f) (J := proEtaleModelTopology X)
      (K := proEtaleModelTopology Z) (proEtaleModelRingUnit f R)).IsRightAdjoint := by
    infer_instance
  exact (proEtaleModuleFromModel (X := Z)
    (proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))).mapIso
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (F := proEtaleModelBaseChange f) (J := proEtaleModelTopology X)
      (K := proEtaleModelTopology Z) (proEtaleModelRingUnit f R)))

private def inverseFreeIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (I : Type (u + 1)) :
    (proEtaleModuleInverseImage f R).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I := by
  have : (proEtaleModuleInverseImage f R).IsLeftAdjoint :=
    (proEtaleModuleInverseImage_canonicalUnitComparison f R).choose.isLeftAdjoint
  exact (SheafOfModules.mapFreeIso _ I (regularInverseIso f R).symm).symm

private def overFreeIso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt)
    (I : Type (u + 1)) :
    (SheafOfModules.free (R := proEtaleModuleCoefficients R) I).over U ≅
      SheafOfModules.free I := by
  let F := SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U
  have : F.IsLeftAdjoint := by
    change (SheafOfModules.pushforward (𝟙 ((proEtaleModuleCoefficients R).over U))).IsLeftAdjoint
    infer_instance
  exact (SheafOfModules.mapFreeIso F I (Iso.refl _)).symm

private def powerFreeIso (X : Scheme.{u}) (r : ℕ) :
    AlgebraicGeometry.ProEtale.RationalStratum.freeModel l E X r ≅
      SheafOfModules.free (ULift.{u + 1} (Fin r)) := by
  let R := proEtaleModuleCoefficients (rationalCoefficientSheaf l X E)
  let F := fun _ : Fin r ↦ SheafOfModules.unit R
  let : HasBiproduct F := HasBiproduct.of_hasProduct F
  exact (biproduct.isoProduct F).symm ≪≫ biproduct.isoCoproduct F ≪≫
    (Sigma.reindex Equiv.ulift F).symm

private theorem constantFiniteFree (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E)))
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (hN : Module.FinitePresentation (PbcIntegralRing l E) N) :
    ∃ r : ℕ, Nonempty ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj
      ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin r))) := by
  classical
  let := hN
  let := (AlgebraicGeometry.ProEtale.RationalStratum.inclusion l E).toAlgebra
  let V := AlgebraicGeometry.ProEtale.RationalStratum.vectorSpace l E N
  have : Module.Finite (ULift.{u + 1} E) V := by
    change Module.Finite (ULift.{u + 1} E)
      (TensorProduct (PbcIntegralRing l E) (ULift.{u + 1} E) N)
    exact Module.Finite.base_change _ _ _
  let r := Module.finrank (ULift.{u + 1} E) V
  let b : V ≅ ModuleCat.of (ULift.{u + 1} E) (Fin r → ULift.{u + 1} E) :=
    (Module.finBasis (ULift.{u + 1} E) V).equivFun.toModuleIso
  let c := AlgebraicGeometry.ProEtale.RationalStratum.rationalConstants l E X
  let e := (AlgebraicGeometry.ProEtale.RationalStratum.scalarModels l E X).choose
  let F := constantModuleHomFunctor.{u + 1, u} (ProEt.topology X) (ULift.{u + 1} E) ⋙
    PurScalar.tensorFunctor.{u + 1, u + 1, u} c
  exact ⟨r, ⟨directConstantComparison l E X i hi N ≪≫ e N hN ≪≫ F.mapIso b ≪≫
    ConstantFiniteFreePresentationExtension.beta (ProEt.topology X) (ULift.{u + 1} E)
      (rationalCoefficientSheaf l X E) c r ≪≫ powerFreeIso l E X r⟩⟩

private def extendInverseOverIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules X R) (U : Z.ProEt) :
    ((proEtaleModuleInverseImage f S).obj ((pbcExtend a).obj M)).over U ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (((ProEt.topology Z).overPullback CommRingCat.{u + 1} U).map
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a))
        (((proEtaleModuleInverseImage f R).obj M).over U) := by
  exact (SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage f S).mapIso
        (eqToIso (reductionChange_obj_eq X a M)) ≪≫
        (PurScalar.scalarIso f R S a).app M) ≪≫
    SheafOfModules.scalarOverIso.{u + 1, u, u + 1}
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a) _ U

/-- Ordinary localization of the completed finitely presented local models. -/
theorem rationalModuleLocalModelsTransport (X : Scheme.{u}) [IsNoetherian X]
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (_hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    (∀ M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)),
      IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E) M →
        ∃ s : FiniteLocallyClosedStratification X, ∀ k : Fin s.n,
          ((proEtaleModuleInverseImage (s.immersion k)
            (rationalCoefficientSheaf l X E)).obj
              ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj M)
            ).IsFiniteLocallyFree) ∧
    (∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)),
      Module.FinitePresentation (PbcIntegralRing l E) N →
        Nonempty ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj
          ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
            (adicLisseConstantModules X (ULift.{u + 1} E) ⋙
              pbcExtend (letI := coefficientExtensionNormedField l E
                continuousCoefficientConstantComparison X (ULift.{u + 1} E))).obj
                ((ModuleCat.extendScalars
                  (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)).obj N))) :=
  by
    classical
    refine ⟨?_, fun N hN ↦ ⟨rationalConstantComparison l E X i _hi N hN⟩⟩
    intro M hM
    obtain ⟨s, hs⟩ := hM
    refine ⟨s.toFiniteLocallyClosed, fun k ↦ ?_⟩
    obtain ⟨V, hV, hv⟩ := hs k
    let Z := s.domain k
    let f := s.immersion k
    let a := i.hom ≫ integralRationalCoefficientMap l E X
    let R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E)
    let I := Σ U : Z.ProEt, {g : U ⟶ ⊤_ Z.ProEt // V g}
    let W : I → Z.ProEt := fun j ↦ j.1
    have hW : (ProEt.topology Z).CoversTop W := by
      apply ((ProEt.topology Z).coversTop_iff_of_isTerminal _ terminalIsTerminal W).mpr
      apply (ProEt.topology Z).superset_covering _ hV
      intro U g hg
      exact ⟨⟨U, g, hg⟩, ⟨𝟙 U⟩⟩
    have hlocal : ∀ j : I, ∃ r : ℕ,
        Nonempty (((proEtaleModuleInverseImage f (rationalCoefficientSheaf l X E)).obj
          ((pbcExtend a).obj M)).over (W j) ≅
            SheafOfModules.free (ULift.{u + 1} (Fin r))) := by
      intro j
      obtain ⟨N, hN, ⟨e⟩⟩ := hv j.1 j.2.val j.2.property
      obtain ⟨r, ⟨b⟩⟩ := constantFiniteFree l E X i _hi N hN
      let c := ((ProEt.topology Z).overPullback CommRingCat.{u + 1} (W j)).map
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a)
      let F := PurScalar.tensorFunctor.{u + 1, u + 1, u} c
      let O := SheafOfModules.overFunctor (proEtaleModuleCoefficients R) (W j)
      exact ⟨r, ⟨extendInverseOverIso f a M (W j) ≪≫ F.mapIso e ≪≫
        (extendInverseOverIso f a ((integralConstantModule X (pbcIntegralDatum l E)).obj N)
          (W j)).symm ≪≫
        O.mapIso ((proEtaleModuleInverseImage f (rationalCoefficientSheaf l X E)).mapIso b ≪≫
          inverseFreeIso f (rationalCoefficientSheaf l X E) _) ≪≫
        overFreeIso R (W j) _⟩⟩
    let r : I → ℕ := fun j ↦ (hlocal j).choose
    exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free.{u + 1, u, u + 1} W hW
      (fun j ↦ ULift.{u + 1} (Fin (r j))) (fun j ↦ (hlocal j).choose_spec)

end AlgebraicGeometry.Scheme
