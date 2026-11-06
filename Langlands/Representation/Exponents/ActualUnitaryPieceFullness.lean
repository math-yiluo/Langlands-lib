import Langlands.Representation.Exponents.ActualUnitaryGeometricNonvanishing
import Langlands.Representation.Exponents.ActualUnitaryFullPiece
import Langlands.Representation.Exponents.TemperedInductionQuotientNonvanishing

/-! # The two fullness steps for an actual unitary geometric piece -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryPieceFullnessAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
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
  (haarM : MeasureTheory.Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)
  (hcriterionσ : TemperedSquareIntegrableUnitaryPartStatement.{u, v})

include F hσtemp haarM hσsquare hcriterionσ hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- The inner unitary Jacquet part of an actual nonzero geometric piece
contradicts the exact square-integrability criterion unless its parabolic is full. -/
theorem NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable : IsIso D.p' := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have hnonzero := F.unitaryJacquetPart_ne_bot
  obtain ⟨c, _⟩ := hσsquare.2
  have hchar : σ.HasCentralCharacter c.character := c.acts
  by_contra hproper
  exact hnonzero
    ((hcriterionσ k M hl.isConnectedReductive haarM σ c.character hσtemp hchar).mp
      hσsquare D.P' D.M' D.N' A' D.p' D.l' D.r' a' D.hp' D.hl' D.hr'
        D.hmul' ha' hproper)

variable [MeasurableSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  [hBorelL : letI := leviPointTopology lQ hlQ
    BorelSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  (haarL : MeasureTheory.Measure (rationalPoints L ⧸ Subgroup.center (rationalPoints L)))
  [hhaarL : letI := leviPointTopology lQ hlQ; haarL.IsHaarMeasure]
  (hτsquare : letI := leviPointTopology lQ hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsSquareIntegrableModCenter τ.representation haarL)
  (hcriterionτ : TemperedSquareIntegrableUnitaryPartStatement.{u, w})
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

include F hτtemp haarL hτsquare hcriterionτ hb' hsemisimple hinducingTemp hBorelL hhaarL in
omit hBorelM [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))] in
set_option maxHeartbeats 800000 in
/-- The literal induced unitary piece supplies the second fullness step
by semisimple quotient reversal and the exact square-integrability criterion. -/
theorem NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable
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
  exact isIso_of_squareIntegrable_semisimple_induction_quotient
    hlQ.isConnectedReductive D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ'
    hb' τ (SmoothRep.pullback D.e J₀) hcriterionτ haarL hτsquare hτ
      hsemisimple hτtemp hinducingTemp F.map F.nonzero

include F hσtemp hτtemp haarM hσsquare hcriterionσ hBorelM hhaarM
  haarL hτsquare hcriterionτ hb' hsemisimple hinducingTemp hBorelL hhaarL in
set_option maxHeartbeats 800000 in
/-- Conditional assembly of both actual fullness steps and the existing
original-point conjugacy endpoint. All remaining analytic inputs are explicit. -/
def unitaryPieceConjugacyOfSquareIntegrableNonzeroMap
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible) :
    FullPieceConjugacy (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z) σ τ := by
  letI : IsIso D.p' :=
    NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable
      (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
      (hσtemp := hσtemp) (haarM := haarM) (hσsquare := hσsquare)
      (hcriterionσ := hcriterionσ)
  letI : IsIso D.q' :=
    NonzeroUnitaryPieceMap.isIso_right_of_squareIntegrable
      (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
      (hτtemp := hτtemp) (haarL := haarL) (hτsquare := hτsquare)
      (hcriterionτ := hcriterionτ) (hb' := hb') (hsemisimple := hsemisimple)
      (hinducingTemp := hinducingTemp) hτ
  exact D.unitaryFullPieceConjugacyOfNonzeroMap ha' σ τ hσ hτ F.map F.nonzero

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
