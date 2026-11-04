import Langlands.Global.AdelicSIntegersNoetherianStatement
import Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra
import Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-! # Arithmetic Noetherianity from one-dimensional overrings -/

noncomputable section

universe u

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel

namespace Langlands.Global

private theorem functionField_subalgebra_noetherian
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] (B : Subalgebra k F) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B := by
  classical
  by_cases h : ∃ s : B, Transcendental k (s : F)
  · obtain ⟨s, hs⟩ := h
    let R := Algebra.adjoin k ({(s : F)} : Set F)
    have hR : R ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr s.property)
    let B' : Subalgebra R F :=
      { B.toSubring with algebraMap_mem' := fun a => hR a.property }
    let : FiniteDimensional k⟮(s : F)⟯ F :=
      FunctionField.finiteDimensional_of_adjoin_transcendental hs
    have hB :=
      Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
        (K := k⟮(s : F)⟯) B'
    exact ⟨hB.1, hB.2.1⟩
  · let : Algebra.IsAlgebraic k B := ⟨fun s => by
      apply Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr
      exact not_not.mp (fun hs => h ⟨s, hs⟩)⟩
    let : Field B :=
      (isField_of_isIntegral_of_isField' (inferInstance : Field k).toIsField).toField
    exact ⟨inferInstance, inferInstance⟩

theorem adelicSIntegersNoetherian : AdelicSIntegersNoetherianStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S
    let B : Subalgebra k F :=
      { curvePlaceSIntegers k F S with
        algebraMap_mem' := fun a => (curvePlaceSIntegersConstants k F S a).property }
    exact functionField_subalgebra_noetherian k F B
  · intro K _ _ S
    have h :=
      Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
        (K := K) ((S : Set (FinitePlace K)).integer K)
    exact ⟨h.1, h.2.1⟩

end Langlands.Global
