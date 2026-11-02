import Langlands.Automorphic.OperatorCMUnitaryForm
import Langlands.Representation.Unitary.CompletionTransport
import Langlands.Representation.Unitary.CompletionOperations

/-! # Hilbert transport of actual CM argument pullback -/

noncomputable section
universe uK
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance cmHilbertRationalGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance cmHilbertContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance cmHilbertSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance cmHilbertFormsGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance cmHilbertStableGroup : AddCommGroup (StableAutomorphicFunctions K n) :=
  Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization K n} (b : S.UnitaryForm)

local instance cmHilbertSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual complex-linear CM argument pullback extends to a surjective
isometry of the chosen positive-form Hilbert completions. -/
def completedComplexConjEquiv :=
  (b.finiteForm.comp (CMConjugation.finiteConj K n).toMonoidHom).completedOfEquiv
    S.complexConjFiniteEquiv

end OperatorRealization.UnitaryForm
end Langlands.Automorphic
