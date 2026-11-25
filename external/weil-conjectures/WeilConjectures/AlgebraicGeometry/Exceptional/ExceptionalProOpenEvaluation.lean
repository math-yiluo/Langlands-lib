/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import WeilConjectures.Algebra.Homology.SequenceCoinduced.SystemCoinducedAdjunction
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
import all WeilConjectures.CategoryTheory.Site.SiteAlgebraicCompositionUnitSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent

/-! # Ordinary pro-etale open extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
private local instance (priority := 30000) openEvaluationSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] exceptionalTransportProEtaleCommRingSheafify
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  exceptionalTransportProEtaleTypeSheafify exceptionalTransportProEtaleRingCompose
  exceptionalTransportProEtaleRingSetCompose exceptionalTransportProEtaleAddCommGrpSetCompose
attribute [local irreducible] HasDerivedCategory.standard constantSheaf
attribute [local implicit_reducible] coefficientRings coefficientRingQuotients
attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap

private theorem algebraicOpen_leftExact {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : AlgebraicInverseImage.{u + 1, u + 1, u, u + 1, u}
      (Scheme.proEtaleSheafInverseImage j (Type (u + 1))) R S)
    [A.modules.IsRightAdjoint] : PreservesFiniteLimits A.modules.leftAdjoint := by
  have hL := (Scheme.proEtale_immersion_inverseImage_preservesLimits j).1
  obtain ⟨B, hB⟩ := Scheme.proEtaleAlgebraicInverseImage_exists j R
  let AU := CategoryTheory.inverseImageUniverses A
  let BU := CategoryTheory.inverseImageUniverses B
  obtain ⟨er, her, em, hem, hsm⟩ := CategoryTheory.algebraicComparison
    (Iso.refl (Scheme.proEtaleSheafInverseImage j (Type (u + 1)))) _ _ _ BU AU
  let rc := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso er
  let E := Scheme.proEtaleScalarEquivalence X rc
  let tau : B.modules ⟶ A.modules ⋙ E.functor :=
    { app M := ⟨PresheafOfModules.homMk (em.hom.app M).hom (hsm M)⟩
      naturality := by
        intro M N f
        apply (SheafOfModules.toSheaf _).map_injective
        exact em.hom.naturality f }
  have hTau (M) : IsIso (tau.app M) := by
    have : IsIso ((SheafOfModules.toSheaf _).map (tau.app M)) :=
      inferInstanceAs (IsIso (em.hom.app M))
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have : IsIso tau := NatIso.isIso_of_isIso_app tau
  let U : Z.ProEt := Scheme.ProEt.mk j
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion j)
  obtain ⟨q, ⟨hq⟩⟩ := Scheme.proEtale_ringed_open_comparison U R
  let L := SheafOfModules.localizedModuleExtension R U
  let a := SheafOfModules.localizedModuleAdjunctionIndependent R U
  let ef : Scheme.proEtaleModuleInverseImage j R ≅
      SheafOfModules.localizedModuleRestriction R U ⋙ q.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ q.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight hq q.inverse
  let af : q.functor ⋙ L ⊣ B.modules :=
    ((q.toAdjunction.comp a).ofNatIsoRight ef.symm).ofNatIsoRight (eqToIso hB.symm)
  let re : B.modules ⋙ E.inverse ≅ A.modules :=
    Functor.isoWhiskerRight (asIso tau) E.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ E.unitIso.symm ≪≫ Functor.rightUnitor _
  let adj : E.functor ⋙ q.functor ⋙ L ⊣ A.modules :=
    (E.toAdjunction.comp af).ofNatIsoRight re
  let e := adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint A.modules)
  exact preservesFiniteLimits_of_natIso e

private abbrev coextension (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) :=
  SequenceCoinduced.rightExtension
      (coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) n ⋙
    (coefficientSystemEquivalence (J := Scheme.ProEt.topology T) (O := O)
      (ell := ell)).inverse

private def coextensionAdjunction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) :
    coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n ⊣
      coextension T O ell n :=
  (coefficientSystemEquivalence (J := Scheme.ProEt.topology T) (O := O)
    (ell := ell)).toAdjunction.comp (SequenceCoinduced.adjunction.{u + 1, u, u + 1} _ n)

private theorem coextension_transition (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n k : ℕ) (h : n ≤ k)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) :
    IsIso (((coextension T O ell n).obj M).transition k) := by
  change IsIso (SequenceCoinduced.rightTransition.{u + 1, u, u + 1}
    (coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) n M (Nat.le_succ k))
  rw [SequenceCoinduced.rightTransition_above
    (coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) n M
      (Nat.le_succ k) h]
  infer_instance

private theorem coextension_zero (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n k : ℕ) (h : ¬ n ≤ k)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) :
    IsZero (((coextension T O ell n).obj M).level k) := by
  change IsZero (SequenceCoinduced.rightLevel.{u + 1, u, u + 1}
    (coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) n M k)
  dsimp only [SequenceCoinduced.rightLevel]
  rw [dite_eq_right h]
  exact isZero_zero _

private theorem coextension_counit (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) :
    IsIso ((coextensionAdjunction T O ell n).counit.app M) := by
  let B := coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
  have hc : IsIso ((SequenceCoinduced.adjunction B n).counit.app M) := by
    change IsIso (SequenceCoinduced.coevaluate B n _ M (𝟙 _))
    dsimp only [SequenceCoinduced.coevaluate]
    change IsIso ((𝟙 _) ≫ _ ≫ _)
    rw [Category.id_comp]
    infer_instance
  dsimp only [coextensionAdjunction]
  rw [Adjunction.comp_counit_app]
  infer_instance

private theorem coextension_map_isIso (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ)
    {A : CoefficientSystem.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T) O ell}
    {M : coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n}
    (f : A ⟶ (coextension T O ell n).obj M)
    (hz : ∀ k, ¬ n ≤ k → IsZero (A.level k))
    (ht : ∀ k, n ≤ k → IsIso (A.transition k))
    (hn : IsIso (f.app n)) : IsIso f := by
  have hi (k : ℕ) : IsIso (f.app k) := by
    by_cases hk : n ≤ k
    · induction k, hk using Nat.le_induction with
      | base => exact hn
      | succ k hk ih =>
        have := ht k hk
        have := coextension_transition T O ell n k hk M
        have := ih
        have h : IsIso (f.app (k + 1) ≫
            ((coextension T O ell n).obj M).transition k) := by
          rw [f.comm]
          infer_instance
        exact (isIso_comp_right_iff _ _).mp h
    · exact (hz k hk).isIso (coextension_zero T O ell n k hk M) _
  have : ∀ k, IsIso ((coefficientEvaluation (J := Scheme.ProEt.topology T) k).map f) := hi
  exact (evaluations_jointlyReflect O ell (K := Scheme.ProEt.topology T)).isIso f

variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (I : ExceptionalProOrdinaryImage O ell j)

omit [IsOpenImmersion j] in
private theorem inverse_transition_isIso
    (A : CoefficientSystem.{u + 1, u, u + 1} (J := Scheme.ProEt.topology Z) O ell) (k : ℕ)
    [IsIso (A.transition k)] : IsIso ((I.inverse.obj A).transition k) := by
  have h : IsIso ((I.inverse.obj A).transition k ≫
      (coefficientRestriction (J := Scheme.ProEt.topology X) O ell
        (Nat.le_succ k)).map ((I.inverseEvaluation k).hom.app A)) := by
    rw [I.inverseTransition]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

omit [IsOpenImmersion j] in
private theorem coextension_mate_isIso (n : ℕ) :
    IsIso (mateEquiv (coextensionAdjunction Z O ell n)
      (coextensionAdjunction X O ell n) (I.inverseEvaluation n).hom) := by
  let beta := (mateEquiv (coextensionAdjunction Z O ell n)
    (coextensionAdjunction X O ell n) (I.inverseEvaluation n).hom)
  have hi (M) : IsIso (beta.app M) := by
    apply coextension_map_isIso X O ell n (beta.app M)
    · intro k hk
      let e := (I.inverseEvaluation k).app ((coextension Z O ell n).obj M)
      exact e.isZero_iff.mpr ((I.lift k).modules.map_isZero
        (coextension_zero Z O ell n k hk M))
    · intro k hk
      have := coextension_transition Z O ell n k hk M
      exact inverse_transition_isIso O ell j I _ k
    · have := coextension_counit Z O ell n M
      have := coextension_counit X O ell n ((I.lift n).modules.obj M)
      have h : IsIso ((beta.app M).app n ≫
          (coextensionAdjunction X O ell n).counit.app ((I.lift n).modules.obj M)) := by
        change IsIso ((coefficientEvaluation (J := Scheme.ProEt.topology X) n).map
          (beta.app M) ≫ _)
        rw [mateEquiv_counit]
        infer_instance
      exact (isIso_comp_right_iff _ _).mp h
  exact NatIso.isIso_of_isIso_app beta

/-- Level extension by zero is exact, and the mate of ordinary restriction
with evaluation is invertible for the canonical open left adjoints.

Source: Stacks 03DJ, 0941; Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-sf-pro-open-evaluation-mate).

Proof: use the direct-sum and sheafification construction of extension by zero
on the localized pro-etale site. It is exact, since its stalks are the original
stalk on the open and zero off the open. The same conclusion follows from the
exact localized module extension functor. On the vertical sequence site this
construction commutes with evaluation: both evaluate to the direct sum indexed
by the same lifts of a section into the open, with the same coefficient action.
The comparison is the mate of I.inverseEvaluation: the open unit sends a section
to its corresponding summand, and this description is unchanged by evaluation.
The universal property of left adjoints transports this calculation to the
canonical choices used in the statement. Restriction of scalars changes only
the scalar action, so the comparison respects successor transitions. Thus the
mate is invertible as a natural transformation, including for the empty open
and zero ring. -/
theorem exceptionalProOpen_evaluation
    [I.inverse.IsRightAdjoint]
    [∀ n : ℕ, (I.lift n).modules.IsRightAdjoint] :
    (∀ n : ℕ, PreservesFiniteLimits (I.lift n).modules.leftAdjoint ∧
      PreservesFiniteColimits (I.lift n).modules.leftAdjoint) ∧
    ∀ n : ℕ, IsIso
      (((mateEquiv (Adjunction.ofIsRightAdjoint I.inverse)
        (Adjunction.ofIsRightAdjoint (I.lift n).modules)).symm
          (I.inverseEvaluation n).hom)) := by
  constructor
  · intro n
    constructor
    · exact algebraicOpen_leftExact j _ _ (I.lift n)
    · infer_instance
  · intro n
    have := coextension_mate_isIso O ell j I n
    exact WeilConjectures.SequenceModuleEvaluation.inverseMate_isIso_of_iterated
      (Adjunction.ofIsRightAdjoint I.inverse)
      (Adjunction.ofIsRightAdjoint (I.lift n).modules)
      (coextensionAdjunction X O ell n) (coextensionAdjunction Z O ell n)
      (I.inverseEvaluation n).hom

end AlgebraicGeometry
