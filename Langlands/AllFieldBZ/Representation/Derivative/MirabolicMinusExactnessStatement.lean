import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinus
import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicMinusExactnessStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding MinusExactnessStatement isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter ker_psiMinusQuotient phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
/-- Exactness of the actual unnormalized `Ψ⁻`, unnormalized `Φ⁻`, normalized `Ψ⁻`
and normalized `Φ⁻` functors, for every `n` and every supplied nontrivial unitary
additive character `ψ`. -/
def MinusExactnessStatement.{uF, uV} (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  (∀ n : ℕ, MapsShortExactIntertwiners (psiMinusUnnormalized.{uV} T n)) ∧
  (∀ n : ℕ, ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    MapsShortExactIntertwiners (phiMinusUnnormalized.{uV} T ψ n)) ∧
  (∀ n : ℕ, MapsShortExactIntertwiners (psiMinus.{uV} T n)) ∧
  (∀ n : ℕ, ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    MapsShortExactIntertwiners (phiMinus.{uV} T ψ n))

end Langlands.AllFieldBZ.Derivative.Mirabolic
