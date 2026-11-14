import Langlands.Automorphic.OperatorRealization

/-! # Evaluation of realized vectors is linear in the scalar

For an operator realization `S`, evaluating the continuous function carried by `c • f`
at an adelic point gives `c` times the value of the function carried by `f`. This single
declaration replaces two identical copies that `CuspidalAdmissible.Reproduction` and
`OperatorScalarCentralCharacter` declared under the same name, which prevented any module
from importing both.
-/

noncomputable section
universe u

set_option autoImplicit false

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

theorem evaluate_toContinuous_smul (c : ℂ) (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (c • f)) x = c * evaluate F n (S.toContinuous f) x :=
  (congrArg (fun φ => evaluate F n φ x) (S.toContinuous.map_smul c f)).trans rfl

end Langlands.Automorphic.OperatorRealization
