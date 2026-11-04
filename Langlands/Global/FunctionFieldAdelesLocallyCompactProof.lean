import Langlands.Global.FunctionFieldAdelesLocallyCompactStatement
import Langlands.Global.FunctionFieldPlaceResidueProof
import Langlands.Global.CurvePlaceCompletionResidue
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Actual arithmetic gives function-field local compactness -/

noncomputable section

universe u

open scoped Valued RestrictedProduct

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Finiteness is proved for the actual completed residue field. -/
theorem curvePlaceCompletionResidue_finite (v : AlgebraicCurve.Place k F) :
    Finite (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) := by
  let : Module.Finite k v.ResidueField := functionFieldPlaceResidue k F v
  let : Finite v.ResidueField := Module.finite_of_finite k
  exact Finite.of_equiv v.ResidueField (curvePlaceCompletionResidueEquiv v).toEquiv

/-- The actual completed valuation ring is compact. -/
theorem curvePlaceCompletionIntegers_compactSpace (v : AlgebraicCurve.Place k F) :
    CompactSpace (curvePlaceCompletionIntegers v) := by
  let : Finite (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) :=
    curvePlaceCompletionResidue_finite k F v
  let : CompleteSpace (curvePlaceCompletionIntegers v) :=
    (Valued.isClosed_valuationSubring (curvePlaceCompletion v)).isComplete.completeSpace_coe
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := curvePlaceCompletion v) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
    ⟨inferInstanceAs (CompleteSpace (curvePlaceCompletionIntegers v)),
      inferInstanceAs (IsDiscreteValuationRing (curvePlaceCompletionIntegers v)),
      inferInstanceAs (Finite (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)))⟩

/-- The compact open integer ring is a compact neighborhood of zero. -/
theorem curvePlaceCompletion_locallyCompactSpace (v : AlgebraicCurve.Place k F) :
    LocallyCompactSpace (curvePlaceCompletion v) := by
  have hcompact : IsCompact (curvePlaceCompletionIntegers v : Set (curvePlaceCompletion v)) :=
    isCompact_iff_compactSpace.mpr (curvePlaceCompletionIntegers_compactSpace k F v)
  exact hcompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (curvePlaceCompletionIntegers v).zero_mem)

/-- Compact open actual integer rings give a locally compact restricted product. -/
theorem curvePlaceAdeles_locallyCompactSpace : LocallyCompactSpace (CurvePlaceAdeleRing k F) := by
  let : ∀ v : AlgebraicCurve.Place k F, CompactSpace (curvePlaceCompletionIntegers v) :=
    curvePlaceCompletionIntegers_compactSpace k F
  let : Fact (∀ v : AlgebraicCurve.Place k F,
      IsOpen (curvePlaceCompletionIntegers v : Set (curvePlaceCompletion v))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : AlgebraicCurve.Place k F, [curvePlaceCompletion v, curvePlaceCompletionIntegers v]))

theorem functionFieldAdelesLocallyCompact : FunctionFieldAdelesLocallyCompactStatement.{u} := by
  intro k F _ _ _ _ _ _ _
  let : LocallyCompactSpace (CurvePlaceAdeleRing k F) := curvePlaceAdeles_locallyCompactSpace k F
  let : LocallyCompactSpace (RealAbsoluteValueAdeleRing k F) :=
    (functionFieldAbsoluteValueAdeleHomeomorph k F).locallyCompactSpace_iff.mpr inferInstance
  exact ⟨fun v => ⟨curvePlaceCompletionIntegers_compactSpace k F v,
      curvePlaceCompletion_locallyCompactSpace k F v⟩,
    inferInstance,
    fun S => (isOpen_curvePlaceAdeleLevel k F S).locallyCompactSpace,
    inferInstance,
    fun S => (isOpen_realAbsoluteValueAdeleLevel k F S).locallyCompactSpace⟩

end Langlands.Global
