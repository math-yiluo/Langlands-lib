import Langlands.Automorphic.OperatorSubquotient
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison

/-! # Actual determinant twists of whole-operator automorphic quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

private def scalarCovarianceQuotientEquiv
    {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (η : G →* ℂˣ) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ g f, τ g (e f) = (η g : ℂ) • e (ρ g f)) :
    (Langlands.twist η ρ).Equiv τ :=
  Representation.Equiv.mk e (fun g => by
    apply LinearMap.ext
    intro f
    change e ((η g : ℂ) • ρ g f) = τ g (e f)
    rw [e.map_smul]
    exact (hc g f).symm)

private def inverseConjugatedQuotientEquiv
    {A V W X : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (υ : Representation ℂ A X) (α β : A ≃* A)
    (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] X)
    (he : ∀ a v, τ a (e v) = e (ρ (α a) v))
    (hf : ∀ a w, υ a (f w) = f (τ (β a) w))
    (hInv : β = α.symm) :
    Representation.Equiv ρ υ :=
  Representation.Equiv.mk (e.trans f) (fun a => by
    apply LinearMap.ext
    intro v
    change f (e (ρ a v)) = υ a (f (e v))
    rw [hf, he, hInv, α.apply_symm_apply])

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientTwistRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTwistContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTwistSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTwistFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientTwistStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTwistRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

/-- Multiply the actual numerator and its invariant denominator by the determinant character. -/
def determinantTwist : OperatorSubquotient F n where
  upper := Q.upper.determinantTwist χ hχ
  lower := Q.upper.determinantTwistSubrepresentationOrderIso χ hχ Q.lower

@[simp] theorem determinantTwist_lower_toSubmodule :
    (Q.determinantTwist χ hχ).lower.toSubmodule =
      Q.lower.toSubmodule.map (Q.upper.determinantTwistEquiv χ hχ).toLinearMap := rfl

/-- Actual multiplication on the numerator induces an equivalence of module quotients. -/
def determinantTwistEquiv : Q.Space ≃ₗ[ℂ] (Q.determinantTwist χ hχ).Space :=
  Submodule.Quotient.equiv Q.lower.toSubmodule (Q.determinantTwist χ hχ).lower.toSubmodule
    (Q.upper.determinantTwistEquiv χ hχ).toLinearEquiv rfl

@[simp] theorem determinantTwistEquiv_projection (f : Q.upper.Space) :
    Q.determinantTwistEquiv χ hχ (Q.projection f) =
      (Q.determinantTwist χ hχ).projection (Q.upper.determinantTwistEquiv χ hχ f) := rfl

@[simp] theorem determinantTwistEquiv_symm_projection
    (f : (Q.upper.determinantTwist χ hχ).Space) :
    (Q.determinantTwistEquiv χ hχ).symm ((Q.determinantTwist χ hχ).projection f) =
      Q.projection ((Q.upper.determinantTwistEquiv χ hχ).symm f) := rfl

@[simp] theorem determinantTwistEquiv_mem_lower_iff (f : Q.upper.Space) :
    Q.upper.determinantTwistEquiv χ hχ f ∈ (Q.determinantTwist χ hχ).lower ↔
      f ∈ Q.lower := by
  rw [← (Q.determinantTwist χ hχ).projection_eq_zero_iff,
    ← Q.determinantTwistEquiv_projection, (Q.determinantTwistEquiv χ hχ).map_eq_zero_iff,
    Q.projection_eq_zero_iff]

/-- The induced quotient actions satisfy the actual whole-algebra covariance identity. -/
theorem determinantTwistEquiv_operatorAction
    (a : automorphicOperatorAlgebra F n) (f : Q.Space) :
    (Q.determinantTwist χ hχ).representation a (Q.determinantTwistEquiv χ hχ f) =
      Q.determinantTwistEquiv χ hχ
        (Q.representation (determinantOperatorConjugation n χ hχ a) f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change (Q.determinantTwist χ hχ).projection
      ((Q.upper.determinantTwist χ hχ).representation a
        (Q.upper.determinantTwistEquiv χ hχ v)) =
    (Q.determinantTwist χ hχ).projection
      (Q.upper.determinantTwistEquiv χ hχ
        (Q.upper.representation (determinantOperatorConjugation n χ hχ a) v))
  exact congrArg (Q.determinantTwist χ hχ).projection
    (Q.upper.determinantTwistEquiv_operatorAction χ hχ a v)

theorem determinantTwistEquiv_finite (d : FiniteAdelicGL F n) (f : Q.Space) :
    (Q.determinantTwist χ hχ).finiteRepresentation d (Q.determinantTwistEquiv χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        Q.determinantTwistEquiv χ hχ (Q.finiteRepresentation d f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change (Q.determinantTwist χ hχ).projection
      ((Q.upper.determinantTwist χ hχ).finiteRepresentation d
        (Q.upper.determinantTwistEquiv χ hχ v)) = _
  exact (congrArg (Q.determinantTwist χ hχ).projection
    (Q.upper.determinantTwistEquiv_finite χ hχ d v)).trans
      ((Q.determinantTwist χ hχ).projection.toLinearMap.map_smul _ _)

theorem determinantTwistEquiv_compact (k : standardInfiniteCompact F n) (f : Q.Space) :
    (Q.determinantTwist χ hχ).compactRepresentation k (Q.determinantTwistEquiv χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        Q.determinantTwistEquiv χ hχ (Q.compactRepresentation k f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change (Q.determinantTwist χ hχ).projection
      ((Q.upper.determinantTwist χ hχ).compactRepresentation k
        (Q.upper.determinantTwistEquiv χ hχ v)) = _
  exact (congrArg (Q.determinantTwist χ hχ).projection
    (Q.upper.determinantTwistEquiv_compact χ hχ k v)).trans
      ((Q.determinantTwist χ hχ).projection.toLinearMap.map_smul _ _)

theorem determinantTwistEquiv_differential (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : Q.Space) :
    (Q.determinantTwist χ hχ).envelopingAction a (Q.determinantTwistEquiv χ hχ f) =
      Q.determinantTwistEquiv χ hχ (Q.envelopingAction a f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change (Q.determinantTwist χ hχ).projection
      ((Q.upper.determinantTwist χ hχ).envelopingAction a
        (Q.upper.determinantTwistEquiv χ hχ v)) =
    (Q.determinantTwist χ hχ).projection
      (Q.upper.determinantTwistEquiv χ hχ (Q.upper.envelopingAction a v))
  exact congrArg (Q.determinantTwist χ hχ).projection
    (Q.upper.determinantTwistEquiv_differential χ hχ a v)

/-- Genuine representation equivalence for the actual whole-algebra pullback. -/
def determinantTwistRepresentationEquiv :
    Representation.Equiv
      (Q.representation.comp (determinantOperatorConjugation n χ hχ).toMonoidHom)
      (Q.determinantTwist χ hχ).representation :=
  Representation.Equiv.mk (Q.determinantTwistEquiv χ hχ) (fun a => by
    apply LinearMap.ext
    intro f
    exact (Q.determinantTwistEquiv_operatorAction χ hχ a f).symm)

/-- The existing scalar twist is equivalent to the actual finite quotient action. -/
def determinantTwistFiniteEquiv :
    (Langlands.twist (χ.finiteAdelicDeterminant n).toMonoidHom Q.finiteRepresentation).Equiv
      (Q.determinantTwist χ hχ).finiteRepresentation :=
  scalarCovarianceQuotientEquiv Q.finiteRepresentation
    (Q.determinantTwist χ hχ).finiteRepresentation
    (χ.finiteAdelicDeterminant n).toMonoidHom
    (Q.determinantTwistEquiv χ hχ) (Q.determinantTwistEquiv_finite χ hχ)

def determinantTwistCompactEquiv :
    (Langlands.twist (χ.compactAdelicDeterminant n).toMonoidHom Q.compactRepresentation).Equiv
      (Q.determinantTwist χ hχ).compactRepresentation :=
  scalarCovarianceQuotientEquiv Q.compactRepresentation
    (Q.determinantTwist χ hχ).compactRepresentation
    (χ.compactAdelicDeterminant n).toMonoidHom
    (Q.determinantTwistEquiv χ hχ) (Q.determinantTwistEquiv_compact χ hχ)

@[simp] theorem determinantTwistFiniteEquiv_apply (f : Q.Space) :
    Q.determinantTwistFiniteEquiv χ hχ f = Q.determinantTwistEquiv χ hχ f := rfl

@[simp] theorem determinantTwistCompactEquiv_apply (f : Q.Space) :
    Q.determinantTwistCompactEquiv χ hχ f = Q.determinantTwistEquiv χ hχ f := rfl

/-- All whole-action invariant subspaces correspond under the actual quotient map. -/
def determinantTwistSubrepresentationOrderIso :
    Subrepresentation Q.representation ≃o
      Subrepresentation (Q.determinantTwist χ hχ).representation :=
  conjugatedSubrepresentationOrderIso Q.representation (Q.determinantTwist χ hχ).representation
    (determinantOperatorConjugation n χ hχ).toMulEquiv (Q.determinantTwistEquiv χ hχ)
    (Q.determinantTwistEquiv_operatorAction χ hχ)

theorem determinantTwist_isIrreducible_iff :
    (Q.determinantTwist χ hχ).IsIrreducible ↔ Q.IsIrreducible :=
  (Q.determinantTwistSubrepresentationOrderIso χ hχ).isSimpleOrder_iff.symm

/-- Twisting by the inverse character gives a canonical equivalence with the original action. -/
def determinantTwistInvEquiv :
    Q.Equivalence ((Q.determinantTwist χ hχ).determinantTwist χ⁻¹ hχ.inv) :=
  inverseConjugatedQuotientEquiv Q.representation (Q.determinantTwist χ hχ).representation
    ((Q.determinantTwist χ hχ).determinantTwist χ⁻¹ hχ.inv).representation
    (determinantOperatorConjugation n χ hχ).toMulEquiv
    (determinantOperatorConjugation n χ⁻¹ hχ.inv).toMulEquiv
    (Q.determinantTwistEquiv χ hχ) ((Q.determinantTwist χ hχ).determinantTwistEquiv χ⁻¹ hχ.inv)
    (Q.determinantTwistEquiv_operatorAction χ hχ)
    ((Q.determinantTwist χ hχ).determinantTwistEquiv_operatorAction χ⁻¹ hχ.inv)
    (congrArg AlgEquiv.toMulEquiv (determinantOperatorConjugation_inv n χ hχ))

@[simp] theorem determinantTwistInvEquiv_apply (f : Q.Space) :
    Q.determinantTwistInvEquiv χ hχ f =
      (Q.determinantTwist χ hχ).determinantTwistEquiv χ⁻¹ hχ.inv
        (Q.determinantTwistEquiv χ hχ f) := rfl

end OperatorSubquotient
end Langlands.Automorphic
