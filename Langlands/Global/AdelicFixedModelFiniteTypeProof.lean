import Langlands.Global.AdelicFixedModelFiniteTypeStatement
import Langlands.Global.AdelicFixedModelPointComparisonProof
import Langlands.Global.AdelicSIntegersNoetherianProof

/-! # Arithmetic finite-type specialization of the fixed-model point comparison -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Noetherian arithmetic integer bases discharge local finite presentation. -/
theorem adelicFixedModelFiniteType : AdelicFixedModelFiniteTypeStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X _ _
    let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
      (adelicSIntegersNoetherian.1 k F S).1
    exact (adelicFixedModelPointComparison.1 k F S X).2 inferInstance
  · intro K _ _ S X _ _
    let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
      (adelicSIntegersNoetherian.2 K S).1
    exact (adelicFixedModelPointComparison.2 K S X).2 inferInstance

end Langlands.Global
