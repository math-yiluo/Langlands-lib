import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesUniquenessReduction
import Langlands.Representation.Exponents.ActualUnitaryPieceInducingTempered
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.Representation.Exponents.PositiveExponentsUnitaryVanishing
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.Representation.Exponents.LeviInductionNormalizedTemperedProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Exponents.TemperedGeometricLemmaProof
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedProof

/-! # Proof of the VII.2.6 uniqueness assertion

Renard VII.2.6, Theorem, second assertion (printed p.231 / PDF p.237). The published
reduction `temperedIrreducibleDiscreteSeriesUniqueness_of_inputs` uses the VII.2.4
Lemma only in its forward direction: a square-integrable representation has zero
unitary Jacquet part along every proper parabolic. This module derives that direction
from the published necessity half of Casselman's criterion and the published existence
of parabolic root presentations, reruns the two fullness steps and the conjugacy
assembly with it, and closes the remaining inputs with their published proofs.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- **Forward half of the VII.2.4 Lemma, without temperedness.** A square-integrable
smooth representation of `G(F)` has zero unitary Jacquet part along every proper
actual parabolic, rational Levi and split-component datum. Proof: choose a compatible
parabolic root presentation (published existence), and apply the published necessity
half of Casselman's criterion, whose strictly positive cone excludes the real part `0`
of a unitary exponent for a proper parabolic. -/
theorem squareIntegrable_unitaryJacquetPart_eq_bot :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
        [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
        (haar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
        [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        IsSquareIntegrableModCenter π.representation haar →
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
            ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hsq P M U A p l r a hp hl hr hmul ha hproper
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  exact unitaryJacquetPart_eq_bot_of_positive_exponents hG p l r hp hl hr hmul ha pres π
    hproper
    (arbitraryParabolicCasselmanNecessity k G hG haar π hsq P M U A p l r a hp hl hr hmul
      ha pres)

section Fullness

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance uniquenessProofAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 800000 in
/-- The second fullness step of VII.2.6: a nonzero map from a semisimple tempered
induction onto an irreducible square-integrable tempered representation forces the
parabolic to be full. This is
`isIso_of_squareIntegrable_semisimple_induction_quotient` with its VII.2.4 input
replaced by `squareIntegrable_unitaryJacquetPart_eq_bot`. -/
theorem isIso_of_squareIntegrable_semisimple_induction_quotient_of_necessity
    (hG : IsConnectedReductive G)
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    (haar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
    [haar.IsHaarMeasure]
    (hπsquare : IsSquareIntegrableModCenter π.representation haar)
    (hπ : π.IsIrreducible)
    (hsemisimple : letI := leviPointTopology l hl
      Representation.IsSemisimpleRepresentation
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hπtemp : IsNormalizedExponentTempered hG π)
    (hσtemp : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (F : letI := leviPointTopology l hl
      Representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation)
    (hF : F ≠ 0) : IsIso p := by
  have hnonzero := unitaryJacquetPart_ne_bot_of_semisimple_induction_quotient
    hG p l r hp hl hr hmul ha π σ hπ hsemisimple hπtemp hσtemp F hF
  by_contra hproper
  exact hnonzero
    (squareIntegrable_unitaryJacquetPart_eq_bot k G hG haar π hπsquare
      P M U A p l r a hp hl hr hmul ha hproper)

variable {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
  (ha' : IsSplitComponent a')
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
  (F : D.NonzeroUnitaryPieceMap ha' σ τ)
  (hσtemp : letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive σ)
  (hτtemp : letI := leviPointTopology lQ hlQ
    haveI := hlQ.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsNormalizedExponentTempered hlQ.isConnectedReductive τ)

variable [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  [hBorelM : letI := leviPointTopology l hl
    BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  (haarM : Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)

include F haarM hσsquare hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- The first fullness step of VII.2.6: the inner unitary Jacquet part of a nonzero
actual geometric piece is nonzero, so square-integrability of `σ` forces the inner
parabolic `P' = M ∩ zQz⁻¹` to be full. This is
`NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable` with its VII.2.4 input replaced
by `squareIntegrable_unitaryJacquetPart_eq_bot`. -/
theorem NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable_of_necessity :
    IsIso D.p' := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have hnonzero := F.unitaryJacquetPart_ne_bot
  by_contra hproper
  exact hnonzero
    (squareIntegrable_unitaryJacquetPart_eq_bot k M hl.isConnectedReductive haarM σ
      hσsquare D.P' D.M' D.N' A' D.p' D.l' D.r' a' D.hp' D.hl' D.hr' D.hmul' ha' hproper)

variable [MeasurableSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  [hBorelL : letI := leviPointTopology lQ hlQ
    BorelSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  (haarL : Measure (rationalPoints L ⧸ Subgroup.center (rationalPoints L)))
  [hhaarL : letI := leviPointTopology lQ hlQ; haarL.IsHaarMeasure]
  (hτsquare : letI := leviPointTopology lQ hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsSquareIntegrableModCenter τ.representation haarL)
  {B' : CommGroupScheme (Spec (CommRingCat.of k))} {b' : B'.toGrp ⟶ D.L'}
  (hb' : IsSplitComponent b')
  (hsemisimple : letI := leviPointTopology l hl
    Representation.IsSemisimpleRepresentation (D.unitaryPieceRep ha' σ).ρ)
  (hinducingTemp :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    haveI := D.hlQ'.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace D.q' D.lQ' D.hq' D.hlQ'
    haveI := leviPoints_nonarchimedeanGroup D.q' D.lQ' D.hq' D.hlQ'
    IsNormalizedExponentTempered D.hlQ'.isConnectedReductive
      (SmoothRep.pullback D.e
        (leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ)))

include F hτtemp haarL hτsquare hb' hsemisimple hinducingTemp hBorelL hhaarL in
omit hBorelM [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))] in
set_option maxHeartbeats 800000 in
/-- The second fullness step of VII.2.6 for an actual geometric piece: the induced
unitary piece maps nonzero onto the irreducible square-integrable `τ`, so the outer
parabolic `Q' = L ∩ z⁻¹Pz` is full. This is
`NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable` with its VII.2.4 input
replaced by `squareIntegrable_unitaryJacquetPart_eq_bot`. -/
theorem NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable_of_necessity
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible) : IsIso D.q' := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  let J₀ := leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ
  exact isIso_of_squareIntegrable_semisimple_induction_quotient_of_necessity
    hlQ.isConnectedReductive D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ'
    hb' τ (SmoothRep.pullback D.e J₀) haarL hτsquare hτ
      hsemisimple hτtemp hinducingTemp F.map F.nonzero

include F hσtemp hτtemp haarM hσsquare hBorelM hhaarM
  haarL hτsquare hb' hsemisimple hBorelL hhaarL in
set_option maxHeartbeats 800000 in
/-- Actual-piece conjugacy for VII.2.6 from the two original temperedness inputs and
square-integrability: the first fullness step makes `P'` full, which proves the
temperedness of the inner inducing module; the second fullness step then makes `Q'`
full, and the published full-piece endpoint gives the conjugacy. This is
`unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness` with both
VII.2.4 inputs replaced by `squareIntegrable_unitaryJacquetPart_eq_bot`. -/
def unitaryPieceConjugacyOfSquareIntegrableNonzeroMapOfNecessity
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible) :
    FullPieceConjugacy (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z) σ τ := by
  letI : IsIso D.p' :=
    NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable_of_necessity
      (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
      (haarM := haarM) (hσsquare := hσsquare)
  letI : IsIso D.q' :=
    NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable_of_necessity
      (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
      (hτtemp := hτtemp) (haarL := haarL) (hτsquare := hτsquare)
      (hb' := hb') (hsemisimple := hsemisimple)
      (hinducingTemp :=
        D.unitaryPieceInducing_isNormalizedExponentTempered_of_left_full ha' σ hσtemp) hτ
  exact D.unitaryFullPieceConjugacyOfNonzeroMap ha' σ τ hσ hτ F.map F.nonzero

end GeometricLemmaIntersectionDatum

end Fullness

/-- Renard VII.2.6, Theorem, second assertion, from VII.2.1 Remark 2 alone: every other
input of the published reduction is now a published theorem, and its VII.2.4 input is
replaced by `squareIntegrable_unitaryJacquetPart_eq_bot`. -/
theorem temperedIrreducibleDiscreteSeriesUniqueness_of_squareIntegrableTempered
    (hSq : SquareIntegrableNormalizedTemperedStatement.{u, v}) :
    TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v} := by
  have hInd := leviInductionNormalizedTempered.{u, v}
  have hCompact := arbitraryParabolicQuotientCompact.{u}
  have hGeom := temperedGeometricLemma.{u, v}
  have hUnimod := RationalPointFamily.rationalReductiveUnimodularity.{u}
  have hStandard := standardCocharacter.{u}
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hπ P₁ M₁ U₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ σ₁ hσ₁ hσ₁sq hi₁
    P₂ M₂ U₂ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ σ₂ hσ₂ hσ₂sq hi₂
  obtain ⟨i₁, hi₁⟩ := hi₁
  obtain ⟨i₂, hi₂⟩ := hi₂
  have hM₁ := hl₁.isConnectedReductive
  have hM₂ := hl₂.isConnectedReductive
  have := hM₁.isAffineHom
  have := hM₂.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₁) := leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) := leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have : LocallyCompactSpace (rationalPoints M₂) := leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) := leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  have : IsAffine M₁.X.left := isAffine_of_isAffineHom M₁.X.hom
  have : IsAffine M₂.X.left := isAffine_of_isAffineHom M₂.X.hom
  have : T2Space (rationalPoints M₁) := rationalPoint_t2Space k M₁
  have : T2Space (rationalPoints M₂) := rationalPoint_t2Space k M₂
  let : MeasurableSpace (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁)) := borel _
  have : BorelSpace (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁)) := ⟨rfl⟩
  let : MeasurableSpace (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂)) := borel _
  have : BorelSpace (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂)) := ⟨rfl⟩
  let haar₁ : Measure (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁)) :=
    Measure.haar
  let haar₂ : Measure (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂)) :=
    Measure.haar
  have hσ₁temp : IsNormalizedExponentTempered hM₁ σ₁ := hSq k M₁ hM₁ haar₁ σ₁ (hσ₁sq haar₁)
  have hσ₂temp : IsNormalizedExponentTempered hM₂ σ₂ := hSq k M₂ hM₂ haar₂ σ₂ (hσ₂sq haar₂)
  have hItemp := hInd k G hG P₁ M₁ U₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ σ₁ hσ₁temp
  let bσ₁ := rationalSquareIntegrableUnimodularForm M₁ hM₁
    (hUnimod k M₁ hM₁ hStandard) σ₁ hσ₁ hσ₁sq
  have hsemisimple := leviInduction_isSemisimple_of_form hG hUnimod hStandard hCompact
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ σ₁ bσ₁ hItemp
  obtain ⟨AL, aL, haL⟩ := (splitComponentStatement k M₂ hM₂).1
  obtain ⟨m, c, z, hz, D, hD⟩ := hGeom k G hG P₁ M₁ U₁ P₂ M₂ U₂ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ AL aL haL σ₁ hσ₁temp
  choose A' a' ha' using fun i =>
    (splitComponentStatement k (D i).M' (D i).hl'.isConnectedReductive).1
  choose B' b' hb' using fun i =>
    (splitComponentStatement k (D i).L' (D i).hlQ'.isConnectedReductive).1
  obtain ⟨s, e, hs⟩ := hD A' a' ha'
  obtain ⟨i, F⟩ := nonzeroUnitaryPieceMapOfInductionEmbeddings hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ haL π σ₁ σ₂ hπ hsemisimple hItemp hσ₂temp i₁ hi₁ i₂ hi₂
    D ha' s e hs
  have : IsIso (D i).p' :=
    GeometricLemmaIntersectionDatum.NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable_of_necessity
      (D := D i) (ha' := ha' i) (σ := σ₁) (τ := σ₂) (F := F)
      (haarM := haar₁) (hσsquare := hσ₁sq haar₁)
  have hpiece := (D i).unitaryPieceRep_isSemisimple_of_left_full (ha' i) hInd hCompact
    hUnimod hStandard σ₁ hσ₁temp bσ₁ σ₂ hσ₂temp
  let C :=
    GeometricLemmaIntersectionDatum.unitaryPieceConjugacyOfSquareIntegrableNonzeroMapOfNecessity
      (D := D i) (ha' := ha' i) (σ := σ₁) (τ := σ₂) (F := F)
      (hσtemp := hσ₁temp) (hτtemp := hσ₂temp)
      (haarM := haar₁) (hσsquare := hσ₁sq haar₁)
      (haarL := haar₂) (hτsquare := hσ₂sq haar₂)
      (hb' := hb' i) (hsemisimple := hpiece) hσ₁ hσ₂
  exact ⟨(z i)⁻¹, C.leviIso, C.conjugacy, C.linearEquiv, C.intertwines⟩

/-- **Renard VII.2.6, Theorem, second assertion.** If an irreducible tempered
representation embeds in `i_{P₁}^G σ₁` and in `i_{P₂}^G σ₂` with `σ₁`, `σ₂` irreducible
square-integrable, then the two inducing data are conjugate under `G(F)`. -/
theorem temperedIrreducibleDiscreteSeriesUniqueness :
    TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v} :=
  temperedIrreducibleDiscreteSeriesUniqueness_of_squareIntegrableTempered
    squareIntegrableNormalizedTempered

end Langlands.Aubert.General.RepresentedParabolic
