import Langlands.Geometry.Building.Kottwitz.ReductiveMapTorusReduction
import Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessStatement
import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement
import Langlands.GroupScheme.ZExtensionRefinementStatement

/-! # Reductive Kottwitz existence from the remaining structural statements -/

noncomputable section

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- The remaining four structural statements imply the full reductive Kottwitz
existence, independence and surjectivity statement. -/
def ReductiveKottwitzRemainingInputsStatement : Prop :=
  FundamentalInertiaMapStatement.{u} →
  ZExtensionPointSurjectivityStatement.{u} →
  CentralTorusInertiaExactnessStatement.{u} →
  ZExtensionCommonDominationStatement.{u} →
  ReductiveKottwitzExistenceStatement.{u}

/-- All torus, cocenter and descent inputs other than the four explicitly named
structural statements are supplied by published proofs. -/
theorem reductiveKottwitzExistence_of_remaining_inputs :
    ReductiveKottwitzRemainingInputsStatement.{u} := by
  intro hmap hpoint hexact hcommon F _ _ _ _ k _ _ _ _ _ _ G hG
  exact reductiveKottwitzExistenceAt_of_torus_existence hmap F k G hG
    (hpoint k (UnramifiedClosure F) G)
    (fun z => (hexact.zExtension k (UnramifiedClosure F) (SeparableClosure F) z).1)
    (hcommon k G hG)

end Langlands.Geometry.Building.Kottwitz
