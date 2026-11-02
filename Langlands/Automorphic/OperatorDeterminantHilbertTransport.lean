import Langlands.Automorphic.OperatorDeterminantUnitary
import Langlands.Representation.Unitary.CompletionTransport
import Langlands.Representation.Unitary.CompletionOperations

/-! # Hilbert transport of actual finite-order determinant multiplication -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance determinantHilbertRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantHilbertContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantHilbertSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantHilbertFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance determinantHilbertStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n} (b : S.UnitaryForm)
  (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance determinantHilbertSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual finite-order determinant multiplier extends to an isometric
equivalence of the original and actual image positive-form completions. -/
def completedDeterminantTwistEquiv :=
  (b.finiteForm.twist (χ.finiteAdelicDeterminant n).toMonoidHom
    (hχ.isUnitary.norm_finiteAdelicDeterminant n)).completedOfEquiv
      (S.determinantTwistFiniteEquiv χ hχ)

end OperatorRealization.UnitaryForm
end Langlands.Automorphic
