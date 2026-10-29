import Langlands.Representation.Exponents.RefinedOppositeSquareIntegrableConeStatement
import Langlands.Representation.Exponents.RefinedOppositeConeReversal
import Langlands.Representation.Exponents.RefinedUpperSquareIntegrableCone
import Langlands.Representation.Classification.TemperedInductionStatement

/-!
# Proof of the strict blockwise cones for opposite exponents

The analytic hypothesis is tested at one Borel Haar measure on the full central
quotient. Block reversal turns the opposite quotient into the upper quotient of the
reversed refinement, where every real part lies in the open positive root cone
inside each original block; reversing the blocks back gives the cone for `-x`.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric

universe uF uV

/-- Strict blockwise cones for opposite exponents of square-integrable product Levis. -/
theorem refinedOppositeSquareIntegrableCone :
    RefinedOppositeSquareIntegrableConeStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ D σ _ hL2 R χ
  dsimp only
  intro _ hgen x hx
  let := T.leviTopologicalGroup D
  let := borel (D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier))
  have : BorelSpace (D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)) := ⟨rfl⟩
  obtain ⟨μ, _⟩ := T.exists_isHaarMeasure_leviCentralQuotient D
  exact RefinedOppositeConeReversal.blockwiseCone_neg_of_reverse D R
    (RefinedUpperSquareIntegrableCone.isPositiveRootCone T D μ σ.ρ (hL2 μ)
      (ProductLeviDualOpposite.reverseRefinement D R) _
      (RefinedOppositeConeReversal.isGeneralizedEigencharacter_toUpper T D R σ.ρ hgen)
      _ (RefinedOppositeConeReversal.isRealPartOf_relabel T D R hx))

end Langlands.Exponents
