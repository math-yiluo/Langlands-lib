import Langlands.Automorphic.FiniteLocalDeterminantTransport
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-! # Admissibility of actual determinant images -/

noncomputable section
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type uF} [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

include hχ

/-- Finite order makes the actual finite adelic determinant character locally constant. -/
theorem finiteAdelicDeterminant_isLocallyConstant :
    IsLocallyConstant (χ.finiteAdelicDeterminant n) :=
  hχ.isLocallyConstant_pullback
    ((ideleClassMap F).continuous.comp
      ((AdelicGL.determinant F n).continuous.comp (AdelicGL.ofFinite F n).continuous))

/-- The actual finite character kernel is open in the existing finite adelic topology. -/
theorem finiteAdelicDeterminant_isOpen_ker :
    IsOpen ((χ.finiteAdelicDeterminant n).toMonoidHom.ker : Set (FiniteAdelicGL F n)) :=
  (χ.finiteAdelicDeterminant_isLocallyConstant n hχ).isOpen_fiber 1

/-- Finite order also makes the actual completed-local determinant character locally constant. -/
theorem finiteLocalDeterminant_isLocallyConstant (v : FinitePlace F) :
    IsLocallyConstant (χ.finiteLocalDeterminant n v) :=
  (χ.finiteAdelicDeterminant_isLocallyConstant n hχ).comp_continuous
    (FiniteAdelicGL.localInclusion F n v).continuous

/-- The actual local kernel is open in the existing completion matrix topology. -/
theorem finiteLocalDeterminant_isOpen_ker (v : FinitePlace F) :
    IsOpen ((χ.finiteLocalDeterminant n v).toMonoidHom.ker :
      Set (FiniteLocalGL F n v)) :=
  (χ.finiteLocalDeterminant_isLocallyConstant n hχ v).isOpen_fiber 1

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance admissibilityTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance admissibilityTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance admissibilityTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance admissibilityTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteRealization

variable (S : FiniteRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance admissibilityTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual finite adelic multiplication preserves and reflects admissibility. -/
theorem determinantTwist_isAdmissible_iff :
    Langlands.IsAdmissible (S.determinantTwist χ hχ).representation ↔
      Langlands.IsAdmissible S.representation :=
  (Langlands.isAdmissible_iff_of_equiv
    (S.determinantTwistRepresentationEquiv χ hχ)).symm.trans
      (Langlands.isAdmissible_twist_iff
        (χ.finiteAdelicDeterminant n).toMonoidHom S.representation
        (χ.finiteAdelicDeterminant_isOpen_ker n hχ))

end FiniteRealization

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance admissibilityLocalTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual local multiplication preserves and reflects admissibility. -/
theorem determinantTwist_isAdmissible_iff :
    (S.determinantTwist χ hχ).IsAdmissible ↔ S.IsAdmissible :=
  (Langlands.isAdmissible_iff_of_equiv
    (S.determinantTwistRepresentationEquiv χ hχ)).symm.trans
      (Langlands.isAdmissible_twist_iff
        (χ.finiteLocalDeterminant n v).toMonoidHom S.representation
        (χ.finiteLocalDeterminant_isOpen_ker n hχ v))

variable {r : ℕ} (L : LocalRealization F (r + 1) v)

/-- The actual multiplied subspace is a canonical p-adic object, with intrinsic
irreducibility and admissibility proved from those of the original space. -/
def determinantTwistPadicObject (hI : L.IsIrreducible) (hA : L.IsAdmissible) :
    Correspondence.AutomorphicObject.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  (L.determinantTwist χ hχ).padicObject
    ((L.determinantTwist_isIrreducible_iff χ hχ).mpr hI)
    ((L.determinantTwist_isAdmissible_iff χ hχ).mpr hA)

/-- The genuine p-adic class retains the actual multiplied form-space representative. -/
def determinantTwistPadicClass (hI : L.IsIrreducible) (hA : L.IsAdmissible) :
    Correspondence.AutomorphicClass.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Correspondence.automorphicClassOf _ (L.determinantTwistPadicObject χ hχ hI hA)

end LocalRealization
end Langlands.Automorphic
