import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonRecenter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylSectionStatement

/-! # Certified comparison on the actual semistandard components -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

open InvariantComparison WeylOrbits WeylComparison WeylSections
open ActualConjugateLeviCoherence (LeviNormalization)

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

/-- The exact input to the conditional VI.3 comparison. Each arrow uses the
published closed section statement at the same actual source compact. -/
structure WeylSectionComparisonData (hG : IsConnectedReductive G) where
  centralizer_le : ∀ p : SemistandardSpectralIndex i, torusCentralizer i ≤ p.levi
  hasWeylRepresentatives : ∀ p, HasWeylRepresentatives i (d p).compact.toSubgroup
  presentation : ∀ p, CocharacterPresentation hG p
  sameCompact : ∀ p q, (d q).compact = (d p).compact
  normalization : ∀ t : Θ,
    LeviNormalization (presentation t.1).hom
      (dynamicInducing (presentation t.1) (base a ha mu t).obj)
  sourceNormalization : ∀ t : Θ,
    HasIntrinsicSourceNormalization (d t.1) (base a ha mu t) (presentation t.1) (normalization t)
  closedSectionComparison : ∀ (t : Θ) (q : SemistandardSpectralIndex i)
    (n : CompactLift (p := t.1) (q := q) (centralizer_le t.1) (d t.1).compact),
    ClosedSectionComparisonStatement (chosenLeviModel t.1) (chosenLeviModel q) (d t.1) (d q)
      (centralizer_le t.1) n (base a ha mu t) (presentation t.1) (presentation q)
      (sameCompact t.1 q) (normalization t)

namespace WeylSectionComparisonData

variable {a ha mu d} {hG : IsConnectedReductive G}
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)

/-- A compact lift of a relative Weyl transporter for one full source index. -/
abbrev Lift (t : Θ) (q : SemistandardSpectralIndex i) :=
  CompactLift (p := t.1) (q := q) (C.centralizer_le t.1) (d t.1).compact

variable (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q)

set_option hygiene false in
local notation "m" => chosenLeviModel t.1
set_option hygiene false in
local notation "mq" => chosenLeviModel q
set_option hygiene false in
local notation "π" => base a ha mu t
set_option hygiene false in
local notation "hP" => C.centralizer_le t.1
set_option hygiene false in
local notation "πg" => conjugateBase hP (d t.1).compact n π

/-- The original normalization and generic standard-operator specification
give a unique comparison family and a level-preserving smooth realization. -/
private theorem exists_comparison :
    ∃ T : ComparisonFamily m (d t.1) hP n π,
      IsActualFamily m (d t.1) (d q) hP n π (C.presentation t.1) (C.presentation q)
        (C.sameCompact t.1 q) (C.normalization t) T ∧
      InducingNaturality m (d t.1) hP n π T ∧
      ∃ L : smoothOrbitSections m (d t.1) π ≃ₗ[ℂ] smoothOrbitSections mq (d q) πg,
        Realizes m mq (d t.1) (d q) hP n π T L ∧
        RespectsLevels m mq (d t.1) (d q) hP n π L :=
  (C.closedSectionComparison t q n (C.sourceNormalization t)).1

/-- The actual extended normalized comparison on every inducing fiber. -/
def fiberComparison : ComparisonFamily m (d t.1) hP n π :=
  Classical.choose (exists_comparison C t q n)

theorem fiberComparison_isActual :
    IsActualFamily m (d t.1) (d q) hP n π (C.presentation t.1) (C.presentation q)
      (C.sameCompact t.1 q) (C.normalization t) (C.fiberComparison t q n) :=
  (Classical.choose_spec (exists_comparison C t q n)).1

theorem fiberComparison_natural :
    InducingNaturality m (d t.1) hP n π (C.fiberComparison t q n) :=
  (Classical.choose_spec (exists_comparison C t q n)).2.1

set_option maxHeartbeats 1800000 in
/-- V.3.1 gives a bijection at the unit parameter of each actual inducing
representative. The two canonical changes of model preserve bijectivity. -/
theorem fiberComparison_bijective (A : Representatives a ha mu t) :
    Function.Bijective (C.fiberComparison t q n A) := by
  obtain ⟨_, _, _, U, hT⟩ := (C.fiberComparison_isActual t q n).2 A
  obtain ⟨_, _, _, hU⟩ := U.property.2.2
  rw [eq_of_heq hT]
  exact (targetFiberEquiv (C.presentation t.1) (C.presentation q) (d t.1) (d q) hP n A.val.obj).bijective.comp
    ((hU 1).1.comp
      (sourceFiberEquiv (C.presentation t.1) (d t.1) A.val.obj).symm.bijective)

/-- The actual normalized V.3 comparison, viewed as an equivariant equivalence. -/
def fiberComparisonEquiv (A : Representatives a ha mu t) :=
  (C.fiberComparison t q n A).ofBijective (C.fiberComparison_bijective t q n A)

@[simp] theorem fiberComparisonEquiv_apply (A : Representatives a ha mu t)
    (v : orbitFiber A.val) :
    C.fiberComparisonEquiv t q n A v = C.fiberComparison t q n A v := rfl

theorem fiberComparison_unique (T : ComparisonFamily m (d t.1) hP n π)
    (hT : IsActualFamily m (d t.1) (d q) hP n π (C.presentation t.1) (C.presentation q)
      (C.sameCompact t.1 q) (C.normalization t) T) :
    C.fiberComparison t q n = T :=
  (C.closedSectionComparison t q n (C.sourceNormalization t)).2 _ T
    (C.fiberComparison_isActual t q n) hT

/-- The smooth extension supplied by the closed comparison theorem. -/
def smoothComparisonAtConjugateBase :
    smoothOrbitSections m (d t.1) π ≃ₗ[ℂ] smoothOrbitSections mq (d q) πg :=
  Classical.choose (Classical.choose_spec (exists_comparison C t q n)).2.2

theorem smoothComparisonAtConjugateBase_realizes :
    Realizes m mq (d t.1) (d q) hP n π (C.fiberComparison t q n)
      (C.smoothComparisonAtConjugateBase t q n) :=
  (Classical.choose_spec (Classical.choose_spec (exists_comparison C t q n)).2.2).1

theorem smoothComparisonAtConjugateBase_respectsLevels :
    RespectsLevels m mq (d t.1) (d q) hP n π (C.smoothComparisonAtConjugateBase t q n) :=
  (Classical.choose_spec (Classical.choose_spec (exists_comparison C t q n)).2.2).2

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

/-- The intrinsic target of one arrow at the specified actual parabolic. -/
abbrev target :=
  targetIndex a ha mu d t q hP n

/-- The target representative of an actual inducing object in the source orbit. -/
abbrev representative (A : Representatives a ha mu t) :=
  targetRepresentative a ha mu d t q hP n A

/-- The same comparison with its target section recentered at the intrinsic base. -/
def smoothComparison :
    rationalSemistandardThetaComponentSpace a ha mu d t ≃ₗ[ℂ]
      rationalSemistandardThetaComponentSpace a ha mu d (C.target t q n) :=
  (C.smoothComparisonAtConjugateBase t q n).trans (targetRecenter a ha mu d t q hP n).symm

theorem smoothComparison_apply
    (v : rationalSemistandardThetaComponentSpace a ha mu d t) (A : Representatives a ha mu t) :
    (C.smoothComparison t q n v).val (C.representative t q n A) =
      C.fiberComparison t q n A (v.val A) :=
  eq_of_heq (C.smoothComparisonAtConjugateBase_realizes t q n v A)

/-- The inverse on smooth sections evaluates to the inverse of the same
actual normalized comparison on each inducing fiber. -/
theorem smoothComparison_symm_apply
    (v : rationalSemistandardThetaComponentSpace a ha mu d (C.target t q n))
    (A : Representatives a ha mu t) :
    ((C.smoothComparison t q n).symm v).val A =
      (C.fiberComparisonEquiv t q n A).symm (v.val (C.representative t q n A)) := by
  apply (C.fiberComparisonEquiv t q n A).injective
  have hv := congrArg (fun s => s.val (C.representative t q n A))
    ((C.smoothComparison t q n).apply_symm_apply v)
  have h := C.smoothComparison_apply t q n ((C.smoothComparison t q n).symm v) A
  exact h.symm.trans (hv.trans ((C.fiberComparisonEquiv t q n A).apply_symm_apply
    (v.val (C.representative t q n A))).symm)

end WeylSectionComparisonData

end Langlands.HarishChandraSchwartz.RationalSemistandard
