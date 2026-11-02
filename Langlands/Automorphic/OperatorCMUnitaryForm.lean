import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorCMFiniteComparison
import Langlands.Automorphic.OperatorCMTransportClasses
import Langlands.Representation.Unitary.Restriction

/-! # Positive forms on actual CM images of automorphic realizations -/

noncomputable section
universe uK uV uW
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance cmUnitaryRationalGroup :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance cmUnitaryContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance cmUnitarySmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance cmUnitaryFormsGroup :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance cmUnitaryStableGroup :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _
local instance cmUnitarySpaceGroup (S : OperatorRealization K n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization K n} (b : S.UnitaryForm)

private def complexConjFiniteForm :
    Langlands.InvariantPositiveForm S.complexConj.finiteRepresentation :=
  (b.finiteForm.comp (CMConjugation.finiteConj K n).toMonoidHom).ofEquiv
    S.complexConjFiniteEquiv.symm

private def complexConjCompactForm :
    Langlands.InvariantPositiveForm S.complexConj.compactRepresentation :=
  (b.compactForm.comp (CMConjugation.compactConj K n)).ofEquiv
    S.complexConjCompactEquiv.symm

/-- Pull the same positive form through the inverse actual CM image map.
The genuine real Lie direction transforms by the actual real Lie equivalence. -/
def complexConj : S.complexConj.UnitaryForm where
  finiteForm := complexConjFiniteForm b
  compact_invariant := (complexConjCompactForm b).invariant
  real_skew X f g := by
    let e := S.complexConjEquiv.toLinearEquiv
    let Y := ArchimedeanLieTransport.realLieEquiv n
      (NumberField.IsCMField.complexConj K).toRingEquiv X
    let a := ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)
    let a' := ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n Y)
    have ha : ArchimedeanLieTransport.envelopingEquiv n
        (NumberField.IsCMField.complexConj K).toRingEquiv a = a' :=
      ArchimedeanLieTransport.envelopingEquiv_generator n
        (NumberField.IsCMField.complexConj K).toRingEquiv
        (ArchimedeanGL.complexify K n X)
    have he (v : S.Space) :
        S.complexConj.envelopingAction a (e v) = e (S.envelopingAction a' v) :=
      (S.complexConjEquiv_differential a v).trans
        (congrArg (fun z : ArchimedeanGL.EnvelopingAlgebra K n =>
          e (S.envelopingAction z v)) ha)
    have hf := inverse_operator e (S.envelopingAction a')
      (S.complexConj.envelopingAction a) he f
    have hg := inverse_operator e (S.envelopingAction a')
      (S.complexConj.envelopingAction a) he g
    exact (congrArg₂ (fun u v : S.Space =>
      b.inner u (e.symm g) + b.inner (e.symm f) v) hf hg).trans
        (b.real_skew Y (e.symm f) (e.symm g))

@[simp] theorem complexConj_inner (f g : S.complexConj.Space) :
    b.complexConj.inner f g =
      b.inner (S.complexConjEquiv.symm f) (S.complexConjEquiv.symm g) := rfl

/-- The actual CM image equivalence preserves the chosen positive form. -/
@[simp] theorem complexConj_inner_apply (f g : S.Space) :
    b.complexConj.inner (S.complexConjEquiv f) (S.complexConjEquiv g) =
      b.inner f g := by
  exact congrArg₂ (fun u v : S.Space => b.inner u v)
    (S.complexConjEquiv.symm_apply_apply f) (S.complexConjEquiv.symm_apply_apply g)

end OperatorRealization.UnitaryForm

namespace OperatorRealization

theorem IsUnitarizable.complexConj {S : OperatorRealization K n}
    (hS : S.IsUnitarizable) : S.complexConj.IsUnitarizable := by
  obtain ⟨b⟩ := hS
  exact ⟨b.complexConj⟩

/-- Actual CM image formation preserves and reflects unitarizability. -/
theorem complexConj_isUnitarizable_iff (S : OperatorRealization K n) :
    S.complexConj.IsUnitarizable ↔ S.IsUnitarizable := by
  constructor
  · intro h
    have hi := h.complexConj
    rw [complexConj_complexConj] at hi
    exact hi
  · exact IsUnitarizable.complexConj

namespace IsoClass

theorem complexConj_isUnitarizable_iff (c : IsoClass K n) :
    c.complexConj.IsUnitarizable ↔ c.IsUnitarizable := by
  induction c using Quotient.inductionOn with
  | h S => exact OperatorRealization.complexConj_isUnitarizable_iff S

end IsoClass
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] {r : ℕ}

theorem complexConj_isUnitarizable_iff (S : CuspidalOperatorRealization K r) :
    S.complexConj.realization.IsUnitarizable ↔ S.realization.IsUnitarizable :=
  OperatorRealization.complexConj_isUnitarizable_iff S.realization

namespace IsoClass

theorem complexConj_isUnitarizable_iff (c : IsoClass K r) :
    c.complexConj.toOperatorClass.IsUnitarizable ↔ c.toOperatorClass.IsUnitarizable := by
  rw [toOperatorClass_complexConj]
  exact OperatorRealization.IsoClass.complexConj_isUnitarizable_iff c.toOperatorClass

end IsoClass
end CuspidalOperatorRealization
end Langlands.Automorphic
