import Langlands.Representation.Exponents.ArbitraryParabolicTemperedAmbientTransport
import Langlands.Representation.Exponents.NormalizedTemperedSubrepresentation
import Langlands.Representation.Exponents.ActualUnitaryPieceFullness

/-! # Temperedness of the inner inducing module after first fullness -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryInducingTemperedAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

section FullParabolic

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) [IsIso p] (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hG : IsConnectedReductive G)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The literal unitary Jacquet inclusion followed by the full-parabolic
Jacquet equivalence embeds into the original action along the actual Levi map. -/
def fullParabolicUnitaryJacquetEmbedding :
    letI := leviPointTopology l hl
    {j : Representation.IntertwiningMap
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation
      (π.representation.comp (rationalPoints.map (l ≫ p))) //
      Function.Injective j} := by
  let := leviPointTopology l hl
  let E := fullParabolicLeviJacquetEquiv p l hp hl hG r hr hmul π
  let i := SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π)
  exact ⟨E.toIntertwiningMap.comp i,
    E.injective.comp (leviUnitaryJacquetModuleι_injective p l r hp hl hr hmul ha π)⟩

/-- For a full actual parabolic, the unitary part of normalized Jacquet
restriction of a tempered representation is tempered. -/
theorem fullParabolicUnitaryJacquet_isNormalizedExponentTempered
    (hπ : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let e := hl.isoOfIsIsoParabolic (p := p) hG
  have htransport := hπ.pullback_ambientIso hG hl.isConnectedReductive e π
  let j := fullParabolicUnitaryJacquetEmbedding p l r hp hl hr hmul ha hG π
  exact htransport.of_injective_intertwining j.val j.property

end FullParabolic

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
  (hσtemp : letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive σ)

include hσtemp in
set_option maxHeartbeats 800000 in
/-- First fullness suffices for temperedness of the actual inner inducing
module. The conjugation pullback is the point map of the specified scheme iso. -/
theorem unitaryPieceInducing_isNormalizedExponentTempered_of_left_full [IsIso D.p'] :
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
        (leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ)) := by
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
  have := D.hl'.isConnectedReductive.isAffineHom
  have := D.hlQ'.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace D.p' D.l' D.hp' D.hl'
  have := leviPoints_nonarchimedeanGroup D.p' D.l' D.hp' D.hl'
  have := leviPoints_locallyCompactSpace D.q' D.lQ' D.hq' D.hlQ'
  have := leviPoints_nonarchimedeanGroup D.q' D.lQ' D.hq' D.hlQ'
  let J₀ := leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ
  have hJ : IsNormalizedExponentTempered D.hl'.isConnectedReductive J₀ :=
    fullParabolicUnitaryJacquet_isNormalizedExponentTempered D.p' D.l' D.r'
      D.hp' D.hl' D.hr' D.hmul' ha' hl.isConnectedReductive σ hσtemp
  have he : D.e = ambientIsoPointsEquiv D.φ := by
    exact DFunLike.ext _ _ (fun x => D.e_apply x)
  rw [he]
  exact hJ.pullback_ambientIso D.hl'.isConnectedReductive D.hlQ'.isConnectedReductive D.φ J₀

variable
  (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
  (F : D.NonzeroUnitaryPieceMap ha' σ τ)
  (hτtemp : letI := leviPointTopology lQ hlQ
    haveI := hlQ.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsNormalizedExponentTempered hlQ.isConnectedReductive τ)
  [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  [hBorelM : letI := leviPointTopology l hl
    BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  (haarM : MeasureTheory.Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)
  (hcriterionσ : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
  [MeasurableSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
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

include F hσtemp hτtemp haarM hσsquare hcriterionσ hBorelM hhaarM
  haarL hτsquare hcriterionτ hb' hsemisimple hBorelL hhaarL in
set_option maxHeartbeats 800000 in
/-- Conditional actual-piece conjugacy using only the original two
temperedness inputs; first fullness proves the needed inner temperedness. -/
def unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible) :
    FullPieceConjugacy (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z) σ τ := by
  letI : IsIso D.p' :=
    NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable
      (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
      (hσtemp := hσtemp) (haarM := haarM) (hσsquare := hσsquare)
      (hcriterionσ := hcriterionσ)
  exact unitaryPieceConjugacyOfSquareIntegrableNonzeroMap
    (D := D) (ha' := ha') (σ := σ) (τ := τ) (F := F)
    (hσtemp := hσtemp) (hτtemp := hτtemp)
    (haarM := haarM) (hσsquare := hσsquare) (hcriterionσ := hcriterionσ)
    (haarL := haarL) (hτsquare := hτsquare) (hcriterionτ := hcriterionτ)
    (hb' := hb') (hsemisimple := hsemisimple)
    (hinducingTemp :=
      D.unitaryPieceInducing_isNormalizedExponentTempered_of_left_full ha' σ hσtemp)
    hσ hτ

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
