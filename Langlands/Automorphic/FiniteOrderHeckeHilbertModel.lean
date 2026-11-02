import Langlands.Automorphic.FiniteOrderHeckeUnitaryForm
import Langlands.Representation.Unitary.CompleteModel

/-! # The complete scalar Hilbert model of actual finite-order Hecke lines -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeHilbertGroup1 : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeHilbertGroup2 : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeHilbertGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeHilbertGroup4 : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance heckeHilbertGroup5 : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeHilbertGroup6 : AddCommGroup (realization F n χ hχ).Space :=
  Submodule.addCommGroup _

/-- The actual chosen form completion of the represented character line has
the complete scalar Hilbert model, with coordinates given by identity evaluation. -/
def hilbertScalarEquiv :
    (unitaryForm F n χ hχ).finiteForm.HilbertCompletion ≃ₗᵢ[ℂ] ℂ :=
  (unitaryForm F n χ hχ).finiteForm.completeModelEquiv
    (scalarEquiv F n χ hχ).symm
    (fun f g => (unitaryForm_inner F n χ hχ f g).symm)

end Langlands.Automorphic.FiniteOrderHeckeRealization
