import Langlands.Representation.Exponents.SelfUnitaryPieceMultiplicity
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.Representation.Exponents.TemperedPositiveJacquetExponents

/-! # Multiplicity of self-intersection unitary pieces without the VII.2.4 criterion

The Library results of `SelfUnitaryPieceMultiplicity` take the full Renard VII.2.4
criterion `TemperedSquareIntegrableUnitaryPartStatement` as a hypothesis, but use
only its forward direction: a tempered representation that is square integrable
modulo the center has zero unitary Jacquet part at every proper actual parabolic.
That direction follows from the published necessity half of Casselman's
criterion. This module proves it and restates the self-intersection results
without the criterion hypothesis.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.4, Lemma, forward direction: a normalized-exponent tempered
representation that is square integrable modulo the center has zero unitary
Jacquet part at every actual parabolic that is not an isomorphism. This follows
from the necessity half of Casselman's criterion. -/
theorem unitaryJacquetPart_eq_bot_of_tempered_squareIntegrable
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsNormalizedExponentTempered hG π →
        IsSquareIntegrableModCenter π.representation haar →
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
            ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hπ hsq
  have := hG.smooth
  exact (hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish hG π hπ).1
    (arbitraryParabolicCasselmanNecessity k G hG haar π hsq)

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance selfUnitaryPieceUnconditionalPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
  {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
  (ha' : IsSplitComponent a')
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (hσtemp : letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive σ)
  [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  [hBorelM : letI := leviPointTopology l hl
    BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  (haarM : MeasureTheory.Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)

include hσtemp haarM hσsquare hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- A nonzero map from the actual unitary piece of a self-intersection datum to a
tempered representation that is square integrable modulo the center forces the
first intersection parabolic to be full. -/
theorem isIso_p'_of_squareIntegrable_nonzeroUnitaryPieceMap
    (F : D.NonzeroUnitaryPieceMap ha' σ σ) : IsIso D.p' := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have hnonzero := F.unitaryJacquetPart_ne_bot
  by_contra hproper
  exact hnonzero
    (unitaryJacquetPart_eq_bot_of_tempered_squareIntegrable M hl.isConnectedReductive haarM σ
      hσtemp hσsquare D.P' D.M' D.N' A' D.p' D.l' D.r' a' D.hp' D.hl' D.hr' D.hmul' ha'
      hproper)

include hσtemp haarM hσsquare hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- For a tempered irreducible representation that is square integrable modulo
the center, every self-intersection unitary piece has at most a one-dimensional
space of maps to it. -/
theorem unitaryPieceHom_rank_le_one_of_squareIntegrable_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    Module.rank ℂ ((D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation) ≤ 1 := by
  let := leviPointTopology l hl
  by_cases h : ∃ F : (D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation, F ≠ 0
  · obtain ⟨F, hF⟩ := h
    have : IsIso D.p' :=
      D.isIso_p'_of_squareIntegrable_nonzeroUnitaryPieceMap ha' σ hσtemp haarM hσsquare ⟨F, hF⟩
    exact D.unitaryPieceHom_rank_le_one_of_isIso ha' σ hσ hσsquare.1
  · push Not at h
    have : Subsingleton
        ((D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one

include hσtemp haarM hσsquare hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- A nonzero map from a self-intersection unitary piece to the tempered
square-integrable irreducible inducing representation gives the actual
conjugacy of that representation with itself by the inverse of `z`. -/
def selfUnitaryPieceConjugacyOfNonzeroMap_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (F : D.NonzeroUnitaryPieceMap ha' σ σ) :
    FullPieceConjugacy (p := p) (l := l) (q := p) (lQ := l)
      (hl := hl) (hlQ := hl) (z := z) σ σ := by
  haveI : IsIso D.p' :=
    D.isIso_p'_of_squareIntegrable_nonzeroUnitaryPieceMap ha' σ hσtemp haarM hσsquare F
  haveI := D.isIso_q'_of_isIso_p'
  exact D.unitaryFullPieceConjugacyOfNonzeroMap ha' σ σ hσ hσ F.map F.nonzero

include hσtemp haarM hσsquare hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- For a regular tempered square-integrable irreducible representation, a
self-intersection unitary piece with a nonzero map to it has its double-coset
representative in the literal Levi point image. -/
theorem mem_pointImage_of_unitaryPieceHom_ne_zero_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (F : D.NonzeroUnitaryPieceMap ha' σ σ) :
    z ∈ pointImage (l ≫ p) :=
  (D.selfUnitaryPieceConjugacyOfNonzeroMap_unconditional ha' σ hσtemp haarM hσsquare hσ
    F).mem_pointImage_of_isNormalizerRegular hreg

section Selected

variable [Smooth G.X.hom] (hcompact : ArbitraryParabolicQuotientCompactStatement.{u})
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
  (hJac : haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).IsAdmissible)

include ha' hσtemp haarM hσsquare hBorelM hhaarM hcompact pres hJac in
set_option maxHeartbeats 800000 in
/-- The zero-real-part selected part, for the split component of `M`, of a
self-intersection geometric-lemma piece has Hom length at most one into the
tempered square-integrable irreducible inducing representation. -/
theorem selectedPieceHomLength_le_one_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    HomSpace.length
      (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
        ha.isCentralSplitTorus.isCentral.map_mem_center
        (fun χ => Plancherel.SplitTorus.normalizedRealPart
          ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≤ 1 := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨e⟩ := D.nonempty_selectedWeightPart_pieceFunctor_equiv hcompact ha pres ha' σ
    hσtemp hJac
  rw [HomSpace.length_congr_left σ.representation e, HomSpace.length,
    Module.length_eq_rank]
  exact Cardinal.toENat_le_one.mpr
    (D.unitaryPieceHom_rank_le_one_of_squareIntegrable_unconditional ha' σ hσtemp haarM
      hσsquare hσ)

include ha' hσtemp haarM hσsquare hBorelM hhaarM hcompact pres hJac in
set_option maxHeartbeats 800000 in
/-- For a regular tempered square-integrable irreducible inducing
representation, a self-intersection piece whose selected part has nonzero Hom
length into it has its double-coset representative in the literal Levi point
image. -/
theorem mem_pointImage_of_selectedPieceHomLength_ne_zero_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (hne : letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      HomSpace.length
        (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
          ha.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≠ 0) :
    z ∈ pointImage (l ≫ p) := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨e⟩ := D.nonempty_selectedWeightPart_pieceFunctor_equiv hcompact ha pres ha' σ
    hσtemp hJac
  rw [HomSpace.length_congr_left σ.representation e, HomSpace.length, Ne,
    Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial] at hne
  obtain ⟨F, hF⟩ := exists_ne (0 : (D.unitaryPieceRep ha' σ).ρ.IntertwiningMap
    σ.representation)
  exact D.mem_pointImage_of_unitaryPieceHom_ne_zero_unconditional ha' σ hσtemp haarM hσsquare
    hσ hreg ⟨F, hF⟩

include ha' hσtemp haarM hσsquare hBorelM hhaarM hcompact pres hJac in
/-- The same conclusion in the parabolic point image. -/
theorem mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero_unconditional
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (hne : letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      HomSpace.length
        (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
          ha.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≠ 0) :
    z ∈ pointImage p :=
  pointImage_comp_le p l (D.mem_pointImage_of_selectedPieceHomLength_ne_zero_unconditional ha'
    σ hσtemp haarM hσsquare hcompact ha pres hJac hσ hreg hne)

end Selected

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
