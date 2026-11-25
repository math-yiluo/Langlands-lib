/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import Mathlib.Order.CompletePartialOrder

/-! # The coefficient quotient cone in the internal module category

Source: Bhatt--Scholze, Lemma 6.8.2(1), and Propositions 3.1.9--3.1.10.
(blueprint: lem-sfb-integral-coefficient-quotient-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.AdicCompletion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The positive coefficient quotients, retaining their integral scalar actions.
Source: Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-sfb-integral-coefficient-quotient-limit). -/
def coefficientSequence : ℕᵒᵖ ⥤ Modules l E X :=
  Functor.ofOpSequence (X := fun n ↦ finiteModule l E X n) (fun n ↦
    (DerivedNakayama.pullback l E X).map (quotientStep l E n))

/-- The actual quotient projections from the regular integral module.
Source: Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-sfb-integral-coefficient-quotient-limit). -/
def coefficientCone : Cone (coefficientSequence l E X) :=
  ⟨𝟙_ (Modules l E X), NatTrans.ofOpSequence (finiteUnit l E X)
    (fun n ↦ by
      dsimp only [coefficientSequence]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (finiteUnit_step l E X n).symm)⟩

private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousCoefficientRingSheaf X A)

private def continuousMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : continuousAb X A ⟶ continuousAb X B :=
  ⟨{ app := fun _ ↦ AddCommGrpCat.ofHom
      (ULift.ringEquiv.symm.toAddEquiv.toAddMonoidHom.comp
        ((f.compLeftContinuous _ hf).toAddMonoidHom.comp ULift.ringEquiv.toAddEquiv.toAddMonoidHom))
     naturality := fun _ _ _ ↦ rfl }⟩

private theorem realization_natural {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    (upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (show Profinite.continuousMapRingSheafOfUniverse A ⟶
            Profinite.continuousMapRingSheafOfUniverse B from
            ⟨{ app := fun _ ↦ RingCat.ofHom
                (ULift.ringEquiv.symm.toRingHom.comp
                  ((f.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
               naturality := fun _ _ _ ↦ rfl }⟩)) ≫
        ContinuousRingUniverse.comparison X B =
      ContinuousRingUniverse.comparison X A ≫ continuousMap X f hf := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison]
  change _ ≫ adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) =
    adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext S x
  rfl

private def continuousSequence : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Functor.ofOpSequence (X := fun n ↦ continuousAb X
    (Padic.coefficientExtensionRing l E (n + 1)))
    (fun n ↦ continuousMap X (Padic.coefficientExtensionTransition l E (n + 1))
      (continuous_transition l E n))

private def continuousCone : Cone (continuousSequence l E X) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨continuousAb X (Padic.coefficientExtensionIntegers l E),
    NatTrans.ofOpSequence (fun n ↦ continuousMap X
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
      continuous_quot_mk) ?_⟩
  intro n
  dsimp only [continuousSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  ext U f
  rfl

private theorem continuousCone_isLimit : Nonempty (IsLimit (continuousCone l E X)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) :=
    Padic.coefficientExtensionPositiveLimitTopology l E
  obtain ⟨⟨e, he, htop⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  have heci : Continuous e.symm := by
    have hc : @Continuous _ _ (Padic.coefficientExtensionPositiveLimitTopology l E)
        (Padic.coefficientExtensionIntegersTopology l E) e.symm := by
      let := Padic.coefficientExtensionIntegersTopology l E
      exact (e.toEquiv.toHomeomorphOfContinuousOpen htop.continuous
        htop.isOpenMap).symm.continuous
    rw [← Scheme.coefficientIntegersTopology_eq l E] at hc
    exact hc
  refine ⟨isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ?_⟩
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget Ab.{u + 1})
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    exact congrArg (fun s ↦ (s.val (op n)).down x) hfg
  · intro s
    let t (n : ℕ) : C(U.unop.left, Padic.coefficientExtensionRing l E (n + 1)) :=
      (s.val (op n)).down
    let b (x : U.unop.left) : Padic.coefficientExtensionPositiveLimit l E :=
      ⟨fun n ↦ t n x, by
        apply Subring.mem_iInf.mpr
        intro n
        have hn := s.property (homOfLE n.le_succ).op
        simp only [Functor.comp_map, continuousSequence,
          Functor.ofOpSequence_map_homOfLE_succ] at hn
        change Padic.coefficientExtensionTransition l E (n + 1) (t (n + 1) x) = t n x
        exact congrArg (fun f ↦ f.down x) hn⟩
    have hb : Continuous b := by
      apply (continuous_induced_rng
        (f := fun x : Padic.coefficientExtensionPositiveLimit l E ↦ x.val)
        (g := b) (t₂ := @Pi.topologicalSpace ℕ
          (fun n ↦ Padic.coefficientExtensionRing l E (n + 1)) (fun _ ↦ ⊥))).mpr
      apply (continuous_pi (T := fun _ ↦ ⊥))
      intro n
      have ht : @Continuous _ _ _ ⊥ (t n) := by
        have hd : topologicalRingQuotientTopology
            (Padic.coefficientExtensionIdeal l E (n + 1)) = ⊥ :=
          @DiscreteTopology.eq_bot (Padic.coefficientExtensionRing l E (n + 1))
            (topologicalRingQuotientTopology (Padic.coefficientExtensionIdeal l E (n + 1)))
            (DerivedNakayama.quotientDiscrete l E (n + 1))
        exact Eq.mp (congrArg (fun τ ↦ @Continuous _ _ _ τ
          (fun x ↦ t n x)) hd) (t n).continuous
      exact ht
    refine ⟨ULift.up (⟨fun x ↦ e.symm (b x), heci.comp hb⟩ :
      C(U.unop.left, Padic.coefficientExtensionIntegers l E)), ?_⟩
    apply Subtype.ext
    funext n
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))
      (e.symm (b x)) = _
    rw [← he]
    exact congrArg (fun t : Padic.coefficientExtensionPositiveLimit l E ↦ t.val n.unop)
      (e.apply_symm_apply (b x))

private def realizationTower : coefficientSequence l E X ⋙ Mod.forget (ring l E X) ≅
    continuousSequence l E X := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e (n : ℕ) := ContinuousRingUniverse.comparison X
    (Padic.coefficientExtensionRing l E (n + 1))
  have he (n : ℕ) : IsIso (e n) := by
    have := DerivedNakayama.quotientDiscrete l E (n + 1)
    have : TotallySeparatedSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
      TotallySeparatedSpace.of_discrete _
    have : TotallyDisconnectedSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
      TotallySeparatedSpace.totallyDisconnectedSpace _
    exact ContinuousRingUniverse.comparison_isIso X _
  let t : coefficientSequence l E X ⋙ Mod.forget (ring l E X) ⟶
      continuousSequence l E X := NatTrans.ofOpSequence e (by
    intro n
    dsimp only [coefficientSequence, continuousSequence, Functor.comp_map]
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
    exact realization_natural X (Padic.coefficientExtensionTransition l E (n + 1))
      (continuous_transition l E n))
  have (n : ℕᵒᵖ) : IsIso (t.app n) := he n.unop
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

private theorem coefficientCone_isLimit : Nonempty (IsLimit (coefficientCone l E X)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : TotallyDisconnectedSpace (Padic.coefficientExtensionIntegers l E) := by
    have h := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
    rw [← Scheme.coefficientIntegersTopology_eq l E] at h
    exact h
  have : IsIso (ContinuousRingUniverse.comparison X
      (Padic.coefficientExtensionIntegers l E)) :=
    ContinuousRingUniverse.comparison_isIso X _
  let e := asIso (ContinuousRingUniverse.comparison X
    (Padic.coefficientExtensionIntegers l E))
  let c := (Mod.forget (ring l E X)).mapCone (coefficientCone l E X)
  have hc : IsLimit ((Cone.postcompose (realizationTower l E X).hom).obj c) := by
    apply IsLimit.ofIsoLimit (continuousCone_isLimit l E X).some
    refine Cone.ext e.symm ?_
    intro n
    change (continuousCone l E X).π.app n = e.inv ≫
      ((Mod.forget (ring l E X)).map ((coefficientCone l E X).π.app n) ≫
        (realizationTower l E X).hom.app n)
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    change e.hom ≫ continuousMap X
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)))
        continuous_quot_mk = _
    exact (realization_natural X
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)))
      continuous_quot_mk).symm
  exact ⟨isLimitOfReflects (Mod.forget (ring l E X))
    ((IsLimit.postcomposeHomEquiv (realizationTower l E X) c) hc)⟩

/-- Continuous integral coefficients are the ordinary inverse limit of their positive
finite quotients, with the specified projections; the quotient transitions are epi.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Propositions 3.1.9--3.1.10.
(blueprint: lem-sfb-integral-coefficient-quotient-limit).

Proof: on each pro-etale object, compatible continuous functions into the finite
quotients give a continuous function into their discrete-product subspace. The
canonical ring homeomorphism from the integers to that subspace gives the unique
integral-valued lift. The continuous-ring realization comparisons commute with all
quotient maps by their adjunction normalization. Transfer the sectionwise limiting
cone through these comparisons. Evaluation, the sheaf-to-presheaf functor and the
internal-module forgetful functor reflect limits, proving the cone assertion with
its specified projections. The coefficient short exact sequences show that every
quotient projection is epi. Each projection factors through the next projection
and the corresponding transition, so that transition is epi as well. All arguments
allow an arbitrary scheme X. -/
theorem integral_coefficient_quotient_limit :
    Nonempty (IsLimit (coefficientCone l E X)) ∧
      ∀ n : ℕ, Epi ((coefficientSequence l E X).map (homOfLE n.le_succ).op) := by
  refine ⟨coefficientCone_isLimit l E X, ?_⟩
  intro n
  dsimp only [coefficientSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  have : Epi (finiteUnit l E X n) :=
    (CoefficientCone.coefficient_ses l E X n).choose_spec.epi_g
  exact epi_of_epi_fac (finiteUnit_step l E X n)

end AlgebraicGeometry.ProEtale.AdicCompletion
