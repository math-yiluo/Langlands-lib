import Langlands.Global.CurvePlacePrincipalSIntegerFinite
import Langlands.Global.AdelicSIntegersDiagram

/-! # Cofinal actual function-field integer rings of finite type over the integers -/

noncomputable section

universe u

open IntermediateField AlgebraicCurve
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Choose an actual nonzero chart denominator whose principal exceptional set
contains the prescribed original places. The given function-field presentation
supplies the transcendental parameter. -/
def curvePlacePrincipalDenominator (S : Finset (Place k F)) :
    {t : CurveModel.chartRing k
      ({algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)} : Set F) //
      t ≠ 0 ∧ S ⊆ curvePlacePrincipalExceptional k F
        (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)) (t : F)} := by
  let s := algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ F := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  exact ⟨(exists_curvePlacePrincipalExceptional_superset k F s S).choose,
    (exists_curvePlacePrincipalExceptional_superset k F s S).choose_spec⟩

/-- An actual original-place integer level above any prescribed finite set. -/
def curvePlacePrincipalLevelAbove (S : Finset (Place k F)) :
    AdelicLevelIndexAbove S :=
  ⟨curvePlacePrincipalExceptional k F
      (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k))
      ((curvePlacePrincipalDenominator k F S).1 : F),
    (curvePlacePrincipalDenominator k F S).2.2⟩

/-- The literal outside-set integer ring at the chosen cofinal level is of
finite type over the original integers. -/
instance curvePlacePrincipalLevelAbove_finiteType (S : Finset (Place k F)) :
    Algebra.FiniteType ℤ
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) := by
  let s := algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ F := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  let : Fact ((curvePlacePrincipalDenominator k F S).1 ≠ 0) :=
    ⟨(curvePlacePrincipalDenominator k F S).2.1⟩
  have h : Algebra.FiniteType k
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) :=
    inferInstanceAs (Algebra.FiniteType k
      (curvePlaceSIntegers k F (curvePlacePrincipalExceptional k F s
        ((curvePlacePrincipalDenominator k F S).1 : F))))
  exact (inferInstance : Algebra.FiniteType ℤ k).trans h

end Langlands.Global
