import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement

/-!
# All-field port of `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
/-- Exactness of the actual derivative `generalLinearDerivative T ψ N k hk` for every
supplied nontrivial unitary additive character `ψ`, every rank `N` and every order
`k ≤ N`. -/
def GeneralLinearDerivativeExactnessStatement.{uF, uV} (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N),
    Mirabolic.MapsShortExactIntertwiners (generalLinearDerivative.{uF, uV} T ψ N k hk)

end Langlands.AllFieldBZ.Derivative
