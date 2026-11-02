import Langlands.Global.CurvePlaceNonemptyLevel

/-! # Colimits over nonempty finite sets of actual curve places -/

universe u

open CategoryTheory Limits

namespace Langlands.Global

/-- Nonempty finite levels cover the actual adeles and give both categorical colimits. -/
def CurvePlaceNonemptyLevelColimitStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Nonempty (AlgebraicCurve.Place k F)],
    (∀ a : CurvePlaceAdeleRing k F,
      ∃ S : CurvePlaceNonemptyLevelIndex k F, a ∈ curvePlaceAdeleLevel k F S.val) ∧
    (∀ (X : Type u) [TopologicalSpace X] (f : CurvePlaceAdeleRing k F → X),
      Continuous f ↔ ∀ S : CurvePlaceNonemptyLevelIndex k F,
        Continuous (f ∘ (curvePlaceAdeleLevel k F S.val).subtype)) ∧
    Nonempty (IsColimit (curvePlaceNonemptyAdeleLevelCocone k F)) ∧
    Nonempty (IsColimit (curvePlaceNonemptyAdeleLevelRingCocone k F))

end Langlands.Global
