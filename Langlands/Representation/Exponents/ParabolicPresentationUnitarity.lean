import Langlands.Representation.Exponents.ArbitraryParabolicUnitarity
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction

/-! # Invariant forms from actual parabolic presentations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Presentation

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {a : A.toGrp ⟶ M} (pres : ParabolicRootPresentation p l a)

local instance presentationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k] in
include hG pres in
/-- An actual compatible root presentation makes the specified Levi projection
continuous in the canonical rational-point topology. -/
theorem continuous_projection_of_presentation :
    Continuous
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : Smooth G.X.hom := hG.smooth
  let χ := CommGroupScheme.groupHom pres.splitComponentCocharacter ≫ a ≫ l ≫ p
  have hP : pointImage p = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, pres.parabolic_eq_splitComponentCocharacter]
  have hM : pointImage (l ≫ p) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, pres.levi_eq_splitComponentCocharacter]
  have hU : pointImage (r ≫ p) =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, pres.range_comp_radical_eq hr]
  generalize isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul = h
  revert h
  rw [hP, hM, hU]
  intro h
  exact continuous_dynamic_projection k G χ

omit [T2Space k] in
include hG pres hr in
/-- Compact subsets of the supplied radical lie in compact subgroups, using
its actual dynamic realization from the presentation. -/
theorem radical_isLimitOfCompactSubgroups_of_presentation :
    Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r ≫ p)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  rw [pointImage_eq_range_carrier, pres.range_comp_radical_eq hr]
  exact BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
    BruhatTits.dynamicUnipotentCompactOpenContainment k G hG _

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

include hG pres in
/-- The full parabolic modulus formula follows from unimodularity of the
specified Levi and an existing compatible presentation. -/
theorem modularCharacter_of_presentation
    (hM :
      letI := leviPointTopology l hl
      letI : LocallyCompactSpace (rationalPoints M) :=
        leviPoints_locallyCompactSpace p l hp hl
      letI : NonarchimedeanGroup (rationalPoints M) :=
        leviPoints_nonarchimedeanGroup p l hp hl
      ∀ m : rationalPoints M, Measure.modularCharacter m = 1) :
    letI : LocallyCompactSpace (pointImage p) :=
      (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
    ∀ q : pointImage p, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter (pointImage (r ≫ p))
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (pointImage p)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).le_normalizer
        q : ℝ≥0) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  let : LocallyCompactSpace (pointImage (r ≫ p)) := hU.locallyCompactSpace
  let : LocallyCompactSpace (pointImage (l ≫ p)) :=
    (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let e := leviPointsEquiv p l hp hl
  have hM' : ∀ m : pointImage (l ≫ p), Measure.modularCharacter m = 1 := by
    intro m
    simpa only [e.apply_symm_apply] using
      (modularCharacter_continuousMulEquiv e (e.symm m)).trans (hM (e.symm m))
  have hδU := isUnimodularModulus_of_isLimitOfCompactSubgroups _ hU
    (radical_isLimitOfCompactSubgroups_of_presentation hG p l r hr pres)
  intro q
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    h.modularCharacter_eq_restrictCharacter_of_unimodular
      (continuous_projection_of_presentation hG p l r hp hr hmul pres) hM'
      (by simpa only [IsUnimodularModulus, HaarModulus.closedNormalizerCharacter_eq]
        using hδU) q

end Presentation

/-- Construct a form on the original irreducible tempered carrier from the
exact discrete-series assertion, reductive unimodularity and actual quotient
compactness. Compatible presentations are extracted from temperedness. -/
def temperedIrreduciblePresentationForm
    (hDiscrete : TemperedIrreducibleDiscreteSeriesStatement.{u, v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsIrreducible → IsNormalizedExponentTempered hG π →
        InvariantPositiveForm π.representation := by
  have := hG.isAffineHom
  letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hirr htemp
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  apply Classical.choice
  obtain ⟨P, M, U, p, l, r, hp, hl, hr, hmul, σ, hσirr, hσsq, f, hf⟩ :=
    (hDiscrete k G hG π hirr).mp htemp
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨pres⟩ := htemp.nonempty_presentation p l a hp hl ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let bσ := rationalSquareIntegrableUnimodularForm M hl.isConnectedReductive
    (hUnimod k M hl.isConnectedReductive hStandard) σ hσirr hσsq
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    hCompact k G hG P p hp
  let bind := leviInductionUnimodularForm p l r hp hr hl hmul
    (hUnimod k G hG hStandard)
    (modularCharacter_of_presentation hG p l r hp hl hr hmul pres
      (hUnimod k M hl.isConnectedReductive hStandard)) σ bσ
  exact ⟨bind.comap f hf⟩

end Langlands.Aubert.General.RepresentedParabolic
