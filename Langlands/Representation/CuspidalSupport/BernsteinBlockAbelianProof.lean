import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements
import Langlands.Representation.Category.ConstituentSerre

/-! # Abelian Bernstein blocks in every carrier universe -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.2: every actual Bernstein block is abelian with its inherited
preadditive structure, for arbitrary independent field and carrier universes. -/
theorem bernsteinBlockAbelian : BernsteinBlockAbelianStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family s
  exact SmoothRep.irreducibleSubquotientsSubcategory_abelian
    (fun π => IsBernsteinInertialSupport i ν family s (SmoothRep.universeLift.{uF} π))

end Langlands.CuspidalSupport
