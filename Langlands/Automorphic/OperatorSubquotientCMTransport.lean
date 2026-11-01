import Langlands.Automorphic.OperatorSubquotient
import Langlands.Automorphic.OperatorCMTransport

/-! # Actual CM transport of whole-operator automorphic quotients -/

noncomputable section
universe uK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

private def twiceConjugatedRepresentationEquiv
    {A V W X : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (υ : Representation ℂ A X) (α : A ≃* A)
    (hα : ∀ a, α (α a) = a) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] X)
    (he : ∀ a v, τ a (e v) = e (ρ (α a) v))
    (hf : ∀ a w, υ a (f w) = f (τ (α a) w)) :
    Representation.Equiv ρ υ :=
  Representation.Equiv.mk (e.trans f) (fun a => by
    apply LinearMap.ext
    intro v
    change f (e (ρ a v)) = υ a (f (e v))
    rw [hf, he, hα])

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance quotientCMRationalGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMFormGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance quotientCMStableGroup : AddCommGroup (StableAutomorphicFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMRealizationGroup (S : OperatorRealization K n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient K n)

/-- Transport both the actual numerator and its invariant denominator by CM pullback. -/
def complexConj : OperatorSubquotient K n where
  upper := Q.upper.complexConj
  lower := Q.upper.complexConjSubrepresentationOrderIso Q.lower

@[simp] theorem complexConj_lower_toSubmodule :
    Q.complexConj.lower.toSubmodule =
      Q.lower.toSubmodule.map Q.upper.complexConjEquiv.toLinearMap := rfl

/-- The actual numerator CM map induces an equivalence of its actual module quotients. -/
def complexConjEquiv : Q.Space ≃ₗ[ℂ] Q.complexConj.Space :=
  Submodule.Quotient.equiv Q.lower.toSubmodule Q.complexConj.lower.toSubmodule
    Q.upper.complexConjEquiv.toLinearEquiv rfl

@[simp] theorem complexConjEquiv_projection (f : Q.upper.Space) :
    Q.complexConjEquiv (Q.projection f) =
      Q.complexConj.projection (Q.upper.complexConjEquiv f) := rfl

@[simp] theorem complexConjEquiv_symm_projection (f : Q.upper.complexConj.Space) :
    Q.complexConjEquiv.symm (Q.complexConj.projection f) =
      Q.projection (Q.upper.complexConjEquiv.symm f) := rfl

/-- Denominator membership transforms by the same concrete numerator map. -/
@[simp] theorem complexConjEquiv_mem_lower_iff (f : Q.upper.Space) :
    Q.upper.complexConjEquiv f ∈ Q.complexConj.lower ↔ f ∈ Q.lower := by
  rw [← Q.complexConj.projection_eq_zero_iff, ← Q.complexConjEquiv_projection,
    Q.complexConjEquiv.map_eq_zero_iff, Q.projection_eq_zero_iff]

/-- Every induced quotient operator transforms by the genuine CM algebra automorphism. -/
theorem complexConjEquiv_operatorAction (a : automorphicOperatorAlgebra K n) (f : Q.Space) :
    Q.complexConj.representation a (Q.complexConjEquiv f) =
      Q.complexConjEquiv (Q.representation (cmOperatorConjugation n a) f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change Q.complexConj.projection
      (Q.upper.complexConj.representation a (Q.upper.complexConjEquiv v)) =
    Q.complexConj.projection
      (Q.upper.complexConjEquiv (Q.upper.representation (cmOperatorConjugation n a) v))
  exact congrArg Q.complexConj.projection (Q.upper.complexConjEquiv_operatorAction a v)

theorem complexConjEquiv_finite (d : FiniteAdelicGL K n) (f : Q.Space) :
    Q.complexConj.finiteRepresentation d (Q.complexConjEquiv f) =
      Q.complexConjEquiv (Q.finiteRepresentation (CMConjugation.finiteConj K n d) f) := by
  change Q.complexConj.representation (finiteOperator K n d) (Q.complexConjEquiv f) =
    Q.complexConjEquiv
      (Q.representation (finiteOperator K n (CMConjugation.finiteConj K n d)) f)
  simpa only [cmOperatorConjugation_finite] using
    Q.complexConjEquiv_operatorAction (finiteOperator K n d) f

theorem complexConjEquiv_compact (k : standardInfiniteCompact K n) (f : Q.Space) :
    Q.complexConj.compactRepresentation k (Q.complexConjEquiv f) =
      Q.complexConjEquiv (Q.compactRepresentation (CMConjugation.compactConj K n k) f) := by
  change Q.complexConj.representation (compactOperator K n k) (Q.complexConjEquiv f) =
    Q.complexConjEquiv
      (Q.representation (compactOperator K n (CMConjugation.compactConj K n k)) f)
  simpa only [cmOperatorConjugation_compact] using
    Q.complexConjEquiv_operatorAction (compactOperator K n k) f

theorem complexConjEquiv_differential (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : Q.Space) :
    Q.complexConj.envelopingAction a (Q.complexConjEquiv f) =
      Q.complexConjEquiv (Q.envelopingAction
        (ArchimedeanLieTransport.envelopingEquiv n
          (NumberField.IsCMField.complexConj K).toRingEquiv a) f) := by
  change Q.complexConj.representation (differentialOperator K n a) (Q.complexConjEquiv f) =
    Q.complexConjEquiv (Q.representation (differentialOperator K n
      (ArchimedeanLieTransport.envelopingEquiv n
        (NumberField.IsCMField.complexConj K).toRingEquiv a)) f)
  simpa only [cmOperatorConjugation_differential] using
    Q.complexConjEquiv_operatorAction (differentialOperator K n a) f

/-- Whole-action covariance as a genuine equivalence with the actual pullback action. -/
def complexConjRepresentationEquiv :
    Representation.Equiv (Q.representation.comp (cmOperatorConjugation n).toMonoidHom)
      Q.complexConj.representation :=
  Representation.Equiv.mk Q.complexConjEquiv (fun a => by
    apply LinearMap.ext
    intro f
    exact (Q.complexConjEquiv_operatorAction a f).symm)

def complexConjFiniteEquiv :
    Representation.Equiv
      (Q.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      Q.complexConj.finiteRepresentation :=
  Representation.Equiv.mk Q.complexConjEquiv (fun d => by
    apply LinearMap.ext
    intro f
    exact (Q.complexConjEquiv_finite d f).symm)

def complexConjCompactEquiv :
    Representation.Equiv (Q.compactRepresentation.comp (CMConjugation.compactConj K n))
      Q.complexConj.compactRepresentation :=
  Representation.Equiv.mk Q.complexConjEquiv (fun k => by
    apply LinearMap.ext
    intro f
    exact (Q.complexConjEquiv_compact k f).symm)

/-- Image and preimage identify all invariant subspaces of the two quotient actions. -/
def complexConjSubrepresentationOrderIso :
    Subrepresentation Q.representation ≃o Subrepresentation Q.complexConj.representation :=
  conjugatedSubrepresentationOrderIso Q.representation Q.complexConj.representation
    (cmOperatorConjugation n).toMulEquiv Q.complexConjEquiv
    Q.complexConjEquiv_operatorAction

theorem complexConj_isIrreducible_iff :
    Q.complexConj.IsIrreducible ↔ Q.IsIrreducible :=
  Q.complexConjSubrepresentationOrderIso.isSimpleOrder_iff.symm

/-- Applying the actual quotient maps twice gives a genuine full-action equivalence. -/
def complexConjTwiceEquiv : Q.Equivalence Q.complexConj.complexConj :=
  twiceConjugatedRepresentationEquiv Q.representation Q.complexConj.representation
    Q.complexConj.complexConj.representation (cmOperatorConjugation n).toMulEquiv
    (cmOperatorConjugation_involutive n) Q.complexConjEquiv Q.complexConj.complexConjEquiv
    Q.complexConjEquiv_operatorAction Q.complexConj.complexConjEquiv_operatorAction

@[simp] theorem complexConjTwiceEquiv_apply (f : Q.Space) :
    Q.complexConjTwiceEquiv f =
      Q.complexConj.complexConjEquiv (Q.complexConjEquiv f) := rfl

end OperatorSubquotient
end Langlands.Automorphic
