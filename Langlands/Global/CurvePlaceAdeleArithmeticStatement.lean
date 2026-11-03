import Langlands.Global.CurvePlaceAdeleDiagonal

/-! # Faithfulness and coherence of actual curve-place adelic maps -/

universe u

namespace Langlands.Global

/-- The level diagonals are faithful, the full function-field diagonal is faithful,
and presentation transport satisfies its identity and composition laws. -/
def CurvePlaceAdeleArithmeticStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
      [Nonempty (AlgebraicCurve.Place k F)]
      (S : Finset (AlgebraicCurve.Place k F)),
    Function.Injective (curvePlaceAdeleLevelDiagonal k F S)) ∧
  (∀ (k F : Type u) [Field k] [PerfectField k] [Field F]
      [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FunctionField k F],
    Function.Injective (curvePlaceAdeleDiagonal k F)) ∧
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F],
    curvePlaceAdeleCongr (AlgEquiv.refl : F ≃ₐ[k] F) =
      RingEquiv.refl (CurvePlaceAdeleRing k F)) ∧
  (∀ (k F F' F'' : Type u) [Field k] [Field F] [Field F'] [Field F'']
      [Algebra k F] [Algebra k F'] [Algebra k F'']
      (e : F ≃ₐ[k] F') (f : F' ≃ₐ[k] F''),
    curvePlaceAdeleCongr (e.trans f) =
      (curvePlaceAdeleCongr e).trans (curvePlaceAdeleCongr f))

end Langlands.Global
