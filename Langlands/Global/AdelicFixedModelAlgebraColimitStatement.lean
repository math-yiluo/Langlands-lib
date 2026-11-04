import Langlands.Global.AdelicFixedModelCocone

/-! # Algebra-colimit targets for actual arithmetic levels above a fixed base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Global

/-- The actual curve-place adele algebra is the colimit of levels above any fixed set. -/
def CurvePlaceFixedModelAlgebraColimit : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    Nonempty (IsColimit (curvePlaceAdeleOverCocone k F S))

/-- The actual full number-field adele algebra is the colimit of levels above any fixed set. -/
def NumberFieldFixedModelAlgebraColimit : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    Nonempty (IsColimit (numberFieldAdeleOverCocone K S))

/-- Both fixed-initial-base algebra universal properties, in an arbitrary common universe. -/
def AdelicFixedModelAlgebraColimitStatement : Prop :=
  CurvePlaceFixedModelAlgebraColimit.{u} ∧ NumberFieldFixedModelAlgebraColimit.{u}

end Langlands.Global
