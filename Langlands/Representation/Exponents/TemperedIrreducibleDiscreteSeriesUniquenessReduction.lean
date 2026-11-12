import Langlands.Representation.Exponents.TemperedUniquenessAssembly
import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesUniquenessStatement
import Langlands.Representation.Exponents.TemperedGeometricLemmaStatement
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement
import Langlands.Representation.Exponents.LeviInductionNormalizedTemperedStatement
import Langlands.Representation.Exponents.ParabolicPresentationUnitarity
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof

/-! # The VII.2.6 uniqueness assertion from named inputs

Renard VII.2.6, Theorem, second assertion (printed p.231 / PDF p.237), derived from
the published statements of VII.2.1 Remark 2, VII.2.2, the VII.2.4 Lemma, VII.2.5,
compactness of every actual parabolic quotient, reductive unimodularity and standard
cocharacters. These inputs are hypotheses here; this module proves none of them.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Semisimplicity

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance uniquenessReductionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- A normalized induction that is normalized-exponent tempered, from a
representation with an invariant positive form, is semisimple, once ambient and
Levi unimodularity and compactness of the parabolic quotient are supplied. The
compatible presentation needed for the modulus identity comes from temperedness of
the induction. -/
theorem leviInduction_isSemisimple_of_form (hG : IsConnectedReductive G)
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (bσ : letI := leviPointTopology l hl; InvariantPositiveForm σ.representation)
    (hItemp : letI := leviPointTopology l hl
      IsNormalizedExponentTempered hG ((leviInductionFunctor p l r hp hr hl hmul).obj σ)) :
    letI := leviPointTopology l hl
    Representation.IsSemisimpleRepresentation
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation := by
  have hMred := hl.isConnectedReductive
  have := hMred.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hCompact k G hG P p hp
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hMred).1
  obtain ⟨pres⟩ := hItemp.nonempty_presentation p l a hp hl ha
  let bI := leviInductionUnimodularForm p l r hp hr hl hmul (hUnimod k G hG hStandard)
    (modularCharacter_of_presentation hG p l r hp hl hr hmul pres
      (hUnimod k M hMred hStandard)) σ bσ
  exact admissibleUnitarySemisimplicity (rationalPoints G)
    (compactOpenCofinal_of_nonarchimedean _) _ _ hItemp.isAdmissible ⟨bI⟩

variable {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

/-- When the first intersection parabolic `P' = M ∩ zQz⁻¹` is full, the literal
unitary geometric piece of a tempered representation with an invariant positive form
is semisimple, given VII.2.2, quotient compactness, unimodularity and a tempered
representation of `L` (which supplies compatible presentations of the parabolics
of `L`). -/
theorem unitaryPieceRep_isSemisimple_of_left_full
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    [IsIso D.p']
    {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
    (ha' : IsSplitComponent a')
    (hInd : LeviInductionNormalizedTemperedStatement.{u, v})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσtemp : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (bσ : letI := leviPointTopology l hl; InvariantPositiveForm σ.representation)
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, v} ℂ (rationalPoints L))
    (hτtemp : letI := leviPointTopology lQ hlQ
      haveI := hlQ.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
      haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
      IsNormalizedExponentTempered hlQ.isConnectedReductive τ) :
    letI := leviPointTopology l hl
    Representation.IsSemisimpleRepresentation (D.unitaryPieceRep ha' σ).ρ := by
  have hMred := hl.isConnectedReductive
  have hLred := hlQ.isConnectedReductive
  have := hMred.isAffineHom
  have := hLred.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let : TopologicalSpace (rationalPoints D.M') := leviPointTopology D.l' D.hl'
  let : TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'
  have := D.hl'.isConnectedReductive.isAffineHom
  have := D.hlQ'.isConnectedReductive.isAffineHom
  have : LocallyCompactSpace (rationalPoints D.M') :=
    leviPoints_locallyCompactSpace D.p' D.l' D.hp' D.hl'
  have : NonarchimedeanGroup (rationalPoints D.M') :=
    leviPoints_nonarchimedeanGroup D.p' D.l' D.hp' D.hl'
  have : LocallyCompactSpace (rationalPoints D.L') :=
    leviPoints_locallyCompactSpace D.q' D.lQ' D.hq' D.hlQ'
  have : NonarchimedeanGroup (rationalPoints D.L') :=
    leviPoints_nonarchimedeanGroup D.q' D.lQ' D.hq' D.hlQ'
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have : T2Space (rationalPoints L) := rationalPoint_t2Space k L
  have : IsAffine D.L'.X.left := isAffine_of_isAffineHom D.L'.X.hom
  have : T2Space (rationalPoints D.L') := rationalPoint_t2Space k D.L'
  let J₀ := leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' σ
  let X := SmoothRep.pullback D.e J₀
  have hX : IsNormalizedExponentTempered D.hlQ'.isConnectedReductive X :=
    D.unitaryPieceInducing_isNormalizedExponentTempered_of_left_full ha' σ hσtemp
  have hI := hInd k L hLred D.Q' D.L' D.U' D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' X hX
  let j := fullParabolicUnitaryJacquetEmbedding D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha'
    hMred σ
  let bJ : InvariantPositiveForm J₀.representation :=
    (bσ.comp (rationalPoints.map (D.l' ≫ D.p'))).comap j.val j.property
  let bX : InvariantPositiveForm X.representation := bJ.comp D.e.toMonoidHom
  have : CompactSpace (Induction.LeftQuotient (pointImage D.q')) :=
    hCompact k L hLred D.Q' D.q' D.hq'
  obtain ⟨B, b, hb⟩ := (splitComponentStatement k D.L' D.hlQ'.isConnectedReductive).1
  obtain ⟨pres⟩ := hτtemp.nonempty_presentation D.q' D.lQ' b D.hq' D.hlQ' hb
  let bI := leviInductionUnimodularForm D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ'
    (hUnimod k L hLred hStandard)
    (modularCharacter_of_presentation hLred D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ'
      pres (hUnimod k D.L' D.hlQ'.isConnectedReductive hStandard)) X bX
  exact admissibleUnitarySemisimplicity (rationalPoints L)
    (compactOpenCofinal_of_nonarchimedean _) _ _ hI.isAdmissible ⟨bI⟩

end GeometricLemmaIntersectionDatum

end Semisimplicity

/-- Renard VII.2.6, Theorem, second assertion, from the published statements of
VII.2.1 Remark 2, VII.2.2, the VII.2.4 Lemma, VII.2.5, actual parabolic quotient
compactness, reductive unimodularity and standard cocharacters. -/
theorem temperedIrreducibleDiscreteSeriesUniqueness_of_inputs
    (hSq : SquareIntegrableNormalizedTemperedStatement.{u, v})
    (hInd : LeviInductionNormalizedTemperedStatement.{u, v})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hSI : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
    (hGeom : TemperedGeometricLemmaStatement.{u, v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u}) :
    TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v} := by
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
    GeometricLemmaIntersectionDatum.NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable
      (D := D i) (ha' := ha' i) (σ := σ₁) (τ := σ₂) (F := F)
      (hσtemp := hσ₁temp) (haarM := haar₁) (hσsquare := hσ₁sq haar₁) (hcriterionσ := hSI)
  have hpiece := (D i).unitaryPieceRep_isSemisimple_of_left_full (ha' i) hInd hCompact
    hUnimod hStandard σ₁ hσ₁temp bσ₁ σ₂ hσ₂temp
  let C := GeometricLemmaIntersectionDatum.unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness
    (D := D i) (ha' := ha' i) (σ := σ₁) (τ := σ₂) (F := F)
    (hσtemp := hσ₁temp) (hτtemp := hσ₂temp)
    (haarM := haar₁) (hσsquare := hσ₁sq haar₁) (hcriterionσ := hSI)
    (haarL := haar₂) (hτsquare := hσ₂sq haar₂) (hcriterionτ := hSI)
    (hb' := hb' i) (hsemisimple := hpiece) hσ₁ hσ₂
  exact ⟨(z i)⁻¹, C.leviIso, C.conjugacy, C.linearEquiv, C.intertwines⟩

set_option linter.defProp false in
/-- The implication proved by `temperedIrreducibleDiscreteSeriesUniqueness_of_inputs`,
as a single term from its seven inputs to the VII.2.6 uniqueness assertion. -/
def temperedIrreducibleDiscreteSeriesUniquenessOfInputs :
    SquareIntegrableNormalizedTemperedStatement.{u, v} →
      LeviInductionNormalizedTemperedStatement.{u, v} →
        ArbitraryParabolicQuotientCompactStatement.{u} →
          TemperedSquareIntegrableUnitaryPartStatement.{u, v} →
            TemperedGeometricLemmaStatement.{u, v} →
              RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
                StandardCocharacterStatement.{u} →
                  TemperedIrreducibleDiscreteSeriesUniquenessStatement.{u, v} :=
  temperedIrreducibleDiscreteSeriesUniqueness_of_inputs

end Langlands.Aubert.General.RepresentedParabolic
