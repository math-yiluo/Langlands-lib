import Langlands.Automorphic.DeterminantTwistAdmissibility
import Langlands.Automorphic.HeckeTwist.FiniteLocalTransport
import Langlands.Global.HeckeDeterminantLocalConstancy
import Langlands.Automorphic.HeckeTwist.OperatorTwistFiniteComparison
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-! # Admissibility of twists by any Hecke determinant character

For an arbitrary Hecke character `χ`, the finite adelic and local determinant characters
have open kernels (`HeckeCharacter.isLocallyConstant_finiteDeterminant`), so twisting a finite
or local realization by `χ ∘ det` preserves and reflects admissibility. This is the
finite-order-free version of `Langlands.Automorphic.DeterminantTwistAdmissibility`.
-/

noncomputable section
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type uF} [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F)

/-- The finite adelic determinant character of any Hecke character is locally constant. -/
theorem finiteAdelicHeckeDeterminant_isLocallyConstant :
    IsLocallyConstant (χ.finiteAdelicDeterminant n) :=
  χ.isLocallyConstant_finiteDeterminant n

/-- The actual finite character kernel is open in the existing finite adelic topology. -/
theorem finiteAdelicHeckeDeterminant_isOpen_ker :
    IsOpen ((χ.finiteAdelicDeterminant n).toMonoidHom.ker : Set (FiniteAdelicGL F n)) :=
  (χ.finiteAdelicHeckeDeterminant_isLocallyConstant n).isOpen_fiber 1

/-- The completed-local determinant character of any Hecke character is locally constant. -/
theorem finiteLocalHeckeDeterminant_isLocallyConstant (v : FinitePlace F) :
    IsLocallyConstant (χ.finiteLocalDeterminant n v) :=
  (χ.finiteAdelicHeckeDeterminant_isLocallyConstant n).comp_continuous
    (FiniteAdelicGL.localInclusion F n v).continuous

/-- The actual local kernel is open in the existing completion matrix topology. -/
theorem finiteLocalHeckeDeterminant_isOpen_ker (v : FinitePlace F) :
    IsOpen ((χ.finiteLocalDeterminant n v).toMonoidHom.ker :
      Set (FiniteLocalGL F n v)) :=
  (χ.finiteLocalHeckeDeterminant_isLocallyConstant n v).isOpen_fiber 1

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance heckeAdmissibilityTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeAdmissibilityTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeAdmissibilityTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeAdmissibilityTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteRealization

variable (S : FiniteRealization F n) (χ : HeckeCharacter F)

local instance heckeAdmissibilityTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual finite adelic multiplication preserves and reflects admissibility. -/
theorem heckeDeterminantTwist_isAdmissible_iff :
    Langlands.IsAdmissible (S.heckeDeterminantTwist χ).representation ↔
      Langlands.IsAdmissible S.representation :=
  (Langlands.isAdmissible_iff_of_equiv
    (S.heckeDeterminantTwistRepresentationEquiv χ)).symm.trans
      (Langlands.isAdmissible_twist_iff
        (χ.finiteAdelicDeterminant n).toMonoidHom S.representation
        (χ.finiteAdelicHeckeDeterminant_isOpen_ker n))

end FiniteRealization

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)
variable (χ : HeckeCharacter F)

local instance heckeAdmissibilityLocalTwistSpaceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Actual local multiplication preserves and reflects admissibility. -/
theorem heckeDeterminantTwist_isAdmissible_iff :
    (S.heckeDeterminantTwist χ).IsAdmissible ↔ S.IsAdmissible :=
  (Langlands.isAdmissible_iff_of_equiv
    (S.heckeDeterminantTwistRepresentationEquiv χ)).symm.trans
      (Langlands.isAdmissible_twist_iff
        (χ.finiteLocalDeterminant n v).toMonoidHom S.representation
        (χ.finiteLocalHeckeDeterminant_isOpen_ker n v))

variable {r : ℕ} (L : LocalRealization F (r + 1) v)

/-- The actual multiplied subspace is a canonical p-adic object, with intrinsic
irreducibility and admissibility proved from those of the original space. -/
def heckeDeterminantTwistPadicObject (hI : L.IsIrreducible) (hA : L.IsAdmissible) :
    Correspondence.AutomorphicObject.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  (L.heckeDeterminantTwist χ).padicObject
    ((L.heckeDeterminantTwist_isIrreducible_iff χ).mpr hI)
    ((L.heckeDeterminantTwist_isAdmissible_iff χ).mpr hA)

/-- The genuine p-adic class retains the actual multiplied form-space representative. -/
def heckeDeterminantTwistPadicClass (hI : L.IsIrreducible) (hA : L.IsAdmissible) :
    Correspondence.AutomorphicClass.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Correspondence.automorphicClassOf _ (L.heckeDeterminantTwistPadicObject χ hI hA)

end LocalRealization
end Langlands.Automorphic
