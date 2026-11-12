import Langlands.Representation.Exponents.TemperedMinimalSquareIntegrable
import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesStatement
import Langlands.Representation.Exponents.TemperedIrreducibleUnitarizableStatement
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement
import Langlands.Representation.Exponents.LeviInductionNormalizedTemperedStatement
import Langlands.Representation.Exponents.NormalizedTemperedSubrepresentation
import Langlands.Representation.Exponents.ParabolicPresentationUnitarity

/-! # The VII.2.6 Theorem (existence) and Corollary from named inputs

Renard VII.2.6, Theorem, first assertion, and Corollary (printed pp.231–232 /
PDF pp.237–238). The existence assertion is derived from the published statements of
VII.2.1 Remark 2, VII.2.2, compactness of every actual parabolic quotient and the
VII.2.4 Lemma. The Corollary is derived from the existence assertion, reductive
unimodularity, standard cocharacters and the same compactness. These inputs are
hypotheses here; this module proves none of them.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Sufficiency

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance discreteSeriesReductionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Renard VII.2.6, sufficiency, conditionally on VII.2.1 Remark 2 and VII.2.2:
a smooth representation with an injective intertwiner into the normalized induction
of a representation that is square-integrable modulo the center for every Haar
measure is normalized-exponent tempered. -/
theorem isNormalizedExponentTempered_of_squareIntegrable_induction_embedding
    (hSq : SquareIntegrableNormalizedTemperedStatement.{u, v})
    (hInd : LeviInductionNormalizedTemperedStatement.{u, v})
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) :=
        leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) :=
        leviPoints_nonarchimedeanGroup p l hp hl
      ∀ [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
        [BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
        (haar : MeasureTheory.Measure
          (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
        [haar.IsHaarMeasure],
        IsSquareIntegrableModCenter σ.representation haar)
    (f : letI := leviPointTopology l hl
      π.representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hf : Function.Injective f) :
    IsNormalizedExponentTempered hG π := by
  have hMred := hl.isConnectedReductive
  have := hMred.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  let : MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M)) := borel _
  have : BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M)) := ⟨rfl⟩
  have hσtemp : IsNormalizedExponentTempered hMred σ :=
    hSq k M hMred MeasureTheory.Measure.haar σ (hσ MeasureTheory.Measure.haar)
  exact (hInd k G hG P M U p l r hp hl hr hmul σ hσtemp).of_injective_intertwining f hf

end Sufficiency

/-- Renard VII.2.6, Theorem, first assertion, from the published statements of
VII.2.1 Remark 2, VII.2.2, actual parabolic quotient compactness and the VII.2.4
square-integrability criterion. -/
theorem temperedIrreducibleDiscreteSeries_of_inputs
    (hSq : SquareIntegrableNormalizedTemperedStatement.{u, v})
    (hInd : LeviInductionNormalizedTemperedStatement.{u, v})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hSI : TemperedSquareIntegrableUnitaryPartStatement.{u, v}) :
    TemperedIrreducibleDiscreteSeriesStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hirr
  constructor
  · intro htemp
    exact htemp.exists_squareIntegrable_induction_embedding hCompact hSI hirr
  · rintro ⟨P, M, U, p, l, r, hp, hl, hr, hmul, σ, -, hσ, f, hf⟩
    exact isNormalizedExponentTempered_of_squareIntegrable_induction_embedding hSq hInd
      p l r hp hl hr hmul σ hσ f hf

/-- Renard VII.2.6, Corollary, from the Theorem's first assertion, reductive
unimodularity, standard cocharacters and actual parabolic quotient compactness. -/
theorem temperedIrreducibleUnitarizable_of_discreteSeries
    (hDiscrete : TemperedIrreducibleDiscreteSeriesStatement.{u, v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u}) :
    TemperedIrreducibleUnitarizableStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hirr htemp
  exact ⟨temperedIrreduciblePresentationForm hDiscrete hUnimod hStandard hCompact
    k G hG π hirr htemp⟩

/-- Renard VII.2.6, Corollary, from all six named inputs. -/
theorem temperedIrreducibleUnitarizable_of_inputs
    (hSq : SquareIntegrableNormalizedTemperedStatement.{u, v})
    (hInd : LeviInductionNormalizedTemperedStatement.{u, v})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hSI : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u}) :
    TemperedIrreducibleUnitarizableStatement.{u, v} :=
  temperedIrreducibleUnitarizable_of_discreteSeries
    (temperedIrreducibleDiscreteSeries_of_inputs hSq hInd hCompact hSI)
    hUnimod hStandard hCompact

set_option linter.defProp false in
/-- The implication proved by `temperedIrreducibleDiscreteSeries_of_inputs`, as a
single term from its four inputs to the VII.2.6 existence assertion. -/
def temperedIrreducibleDiscreteSeriesOfInputs :
    SquareIntegrableNormalizedTemperedStatement.{u, v} →
      LeviInductionNormalizedTemperedStatement.{u, v} →
        ArbitraryParabolicQuotientCompactStatement.{u} →
          TemperedSquareIntegrableUnitaryPartStatement.{u, v} →
            TemperedIrreducibleDiscreteSeriesStatement.{u, v} :=
  temperedIrreducibleDiscreteSeries_of_inputs

end Langlands.Aubert.General.RepresentedParabolic
