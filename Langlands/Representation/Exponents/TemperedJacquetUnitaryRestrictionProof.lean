import Langlands.Representation.Exponents.TemperedJacquetStructure
import Langlands.Representation.Exponents.TemperedJacquetUnitaryRestrictionStatement

/-! # Restriction to the unitary Jacquet part for tempered representations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The Jacquet-side restriction bijection in Renard VII.2.4, with exactly
the published temperedness hypotheses and actual unitary-part inclusion. -/
theorem temperedJacquetUnitaryRestriction :
    TemperedJacquetUnitaryRestrictionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U A p l r a hp hl hr hmul ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π σ hπ hσ
  exact leviUnitaryJacquetRestriction_bijective_of_isCompl p l r hp hl hr hmul ha π σ hσ
    (hπ.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha)

end Langlands.Aubert.General.RepresentedParabolic
