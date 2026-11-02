import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Representation.Unitary.Restriction

/-! # Positive forms on actual whole-carrier local restrictions -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance localUnitaryRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance localUnitaryContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localUnitarySmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localUnitaryFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance localUnitaryStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance localUnitarySpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n} (b : S.UnitaryForm) (v : FinitePlace F)

/-- Restrict the original positive form along the actual one-place inclusion. -/
def localForm : Langlands.InvariantPositiveForm (S.localRepresentation v) :=
  b.finiteForm.comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom

@[simp]
theorem localForm_inner (f g : S.Space) :
    (b.localForm v).inner f g = b.inner f g := rfl

/-- Transfer that form to the actual local restriction of the finite form image. -/
def localImageForm :
    Langlands.InvariantPositiveForm (S.toFiniteRealization.toLocal F n v).representation :=
  (b.localForm v).ofEquiv (S.localFormEquiv v).symm

theorem localImageForm_inner
    (f g : (S.toFiniteRealization.toLocal F n v).Space) :
    (b.localImageForm v).inner f g =
      b.inner ((S.localFormEquiv v).symm f) ((S.localFormEquiv v).symm g) := rfl

/-- The faithful local form inclusion preserves the chosen form exactly. -/
theorem localImageForm_inner_apply (f g : S.Space) :
    (b.localImageForm v).inner (S.localFormEquiv v f) (S.localFormEquiv v g) =
      b.inner f g := by
  change b.inner ((S.localFormEquiv v).symm (S.localFormEquiv v f))
    ((S.localFormEquiv v).symm (S.localFormEquiv v g)) = _
  exact congrArg₂ (fun u w : S.Space => b.inner u w)
    ((S.localFormEquiv v).symm_apply_apply f)
    ((S.localFormEquiv v).symm_apply_apply g)

/-- Transfer the form to the actual zero-denominator module quotient locally. -/
def toSubquotientLocalForm :
    Langlands.InvariantPositiveForm (S.toSubquotient.localRepresentation v) :=
  (b.localForm v).ofEquiv (S.toSubquotientLocalEquiv v).symm

theorem toSubquotientLocalForm_inner (f g : S.toSubquotient.Space) :
    (b.toSubquotientLocalForm v).inner f g =
      b.inner ((S.toSubquotientLocalEquiv v).symm f)
        ((S.toSubquotientLocalEquiv v).symm g) := rfl

/-- The actual zero-denominator projection is an isometry for these forms. -/
theorem toSubquotientLocalForm_inner_projection (f g : S.Space) :
    (b.toSubquotientLocalForm v).inner
      (S.toSubquotient.projection f) (S.toSubquotient.projection g) = b.inner f g := by
  change b.inner
    ((S.toSubquotientLocalEquiv v).symm (S.toSubquotientLocalEquiv v f))
    ((S.toSubquotientLocalEquiv v).symm (S.toSubquotientLocalEquiv v g)) = _
  exact congrArg₂ (fun u w : S.Space => b.inner u w)
    ((S.toSubquotientLocalEquiv v).symm_apply_apply f)
    ((S.toSubquotientLocalEquiv v).symm_apply_apply g)

end OperatorRealization.UnitaryForm

namespace OperatorRealization.IsUnitarizable

variable {S : OperatorRealization F n} (hS : S.IsUnitarizable) (v : FinitePlace F)

include hS

theorem localRestriction : Langlands.IsUnitarizable (S.localRepresentation v) := by
  obtain ⟨b⟩ := hS
  exact ⟨b.localForm v⟩

theorem localImage :
    Langlands.IsUnitarizable (S.toFiniteRealization.toLocal F n v).representation := by
  obtain ⟨b⟩ := hS
  exact ⟨b.localImageForm v⟩

theorem toSubquotientLocal :
    Langlands.IsUnitarizable (S.toSubquotient.localRepresentation v) := by
  obtain ⟨b⟩ := hS
  exact ⟨b.toSubquotientLocalForm v⟩

end OperatorRealization.IsUnitarizable
end Langlands.Automorphic
