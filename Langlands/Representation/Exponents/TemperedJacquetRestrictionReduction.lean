import Langlands.Representation.Exponents.TemperedJacquetRestriction
import Langlands.Representation.Exponents.UnitaryJacquetSplitting
import Langlands.Representation.Exponents.UnitaryJacquetPartTemperedStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement

/-! # The exact unitary restriction target reduced to Jacquet admissibility -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Preservation of admissibility by every actual normalized Jacquet functor
implies the exact VII.2.4 restriction statement. This is a conditional reduction. -/
def TemperedJacquetUnitaryRestrictionReductionStatement : Prop :=
  ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
    TemperedJacquetUnitaryRestrictionStatement.{u, v}

/-- Admissibility of the actual Jacquet module supplies complementarity;
the existing restriction equivalence then gives the literal target map. -/
theorem temperedJacquetUnitaryRestriction_of_jacquetAdmissibility :
    TemperedJacquetUnitaryRestrictionReductionStatement.{u, v} := by
  intro hJ k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U A p l r a hp hl hr hmul ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π σ hπ hσ
  have hJπ := hJ k G hG P M U p l r hp hl hr hmul π hπ.isAdmissible
  exact leviUnitaryJacquetRestriction_bijective_of_isCompl p l r hp hl hr hmul ha π σ hσ
    (unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible
      p l r hp hl hr hmul ha π hJπ)

/-- The exact VII.2.3 statement implies the exact VII.2.4 restriction statement.
Only the complementarity clause of VII.2.3 is needed for this implication. -/
theorem temperedJacquetUnitaryRestriction_of_unitaryJacquetPartTempered
    (h : UnitaryJacquetPartTemperedStatement.{u, v}) :
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
    (h k G hG P M U A p l r a hp hl hr hmul ha π hπ).1

end Langlands.Aubert.General.RepresentedParabolic
