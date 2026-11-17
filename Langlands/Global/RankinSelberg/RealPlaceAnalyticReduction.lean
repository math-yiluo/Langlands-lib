import Langlands.Global.RankinSelberg.RealParameterDeterminant
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-! # Real-place reduction to the analytic restriction equations -/

noncomputable section
universe u

open Langlands.LocalFactor.Archimedean Langlands.Automorphic

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The real standard-module nonvanishing theorem supplies the explicit vector premise. -/
theorem realStandardKFiniteNonzero : RealStandardKFiniteNonzeroStatement := by
  intro ds
  let : Nontrivial (realStandardKFinite (realRank ds) ds) :=
    Langlands.Archimedean.realStandardNontrivial (realRank ds) ds rfl
  exact exists_ne (0 : realStandardKFinite (realRank ds) ds)

/-- The real-place functional equation retains only the analytic restriction equations. -/
def RealPlaceAnalyticReductionStatement : Prop :=
  RealJacquetRestrictionEquationStatement.{u} →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceAnalyticReduction : RealPlaceAnalyticReductionStatement.{u} := by
  intro hJ
  exact realPlaceAnalyticNonzeroReduction hJ realStandardKFiniteNonzero

end Langlands.Global.RankinSelbergGlobal
