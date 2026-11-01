import Langlands.Automorphic.OperatorSubquotientDeterminantTwistClasses
import Langlands.Automorphic.OperatorDeterminantTwistClasses

/-! # The actual finite-order character action on automorphic quotient classes -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientActionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientActionContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientActionSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientActionFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientActionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientActionRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace FiniteSmoothRationalFunctions

@[simp] theorem finiteOrderDeterminantMultiplier_one_apply
    (f : FiniteSmoothRationalFunctions F n) :
    finiteOrderDeterminantMultiplier n 1 HeckeCharacter.hasFiniteOrder_one f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (1 : ℂ) * evaluate F n f.val g = evaluate F n f.val g
  exact one_mul _

/-- Actual multiplication by the product agrees with the two successive multipliers. -/
theorem finiteOrderDeterminantMultiplier_mul_apply
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteOrderDeterminantMultiplier n (χ * ψ) (hχ.mul hψ) f =
      finiteOrderDeterminantMultiplier n ψ hψ
        (finiteOrderDeterminantMultiplier n χ hχ f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change ((χ.adelicDeterminant n g : ℂ) * (ψ.adelicDeterminant n g : ℂ)) *
      evaluate F n f.val g =
    (ψ.adelicDeterminant n g : ℂ) *
      ((χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g)
  ac_rfl

end FiniteSmoothRationalFunctions

@[simp] theorem determinantOperatorConjugation_one_apply
    (a : automorphicOperatorAlgebra F n) :
    determinantOperatorConjugation n 1 HeckeCharacter.hasFiniteOrder_one a = a := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n 1
      HeckeCharacter.hasFiniteOrder_one).symm
      (a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n 1
        HeckeCharacter.hasFiniteOrder_one f)) = a.val f
  apply (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n 1
    HeckeCharacter.hasFiniteOrder_one).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_one_apply,
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_one_apply]

/-- The actual product conjugation is the ordered composite of the two actual conjugations. -/
theorem determinantOperatorConjugation_mul_apply
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder)
    (a : automorphicOperatorAlgebra F n) :
    determinantOperatorConjugation n (χ * ψ) (hχ.mul hψ) a =
      determinantOperatorConjugation n χ hχ (determinantOperatorConjugation n ψ hψ a) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n (χ * ψ)
    (hχ.mul hψ)).injective
  change (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n (χ * ψ)
      (hχ.mul hψ))
      ((FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n (χ * ψ)
        (hχ.mul hψ)).symm
        (a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n (χ * ψ)
          (hχ.mul hψ) f))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply,
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_mul_apply χ ψ hχ hψ]
  change a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n ψ hψ
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) =
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n (χ * ψ) (hχ.mul hψ)
      ((FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).symm
        ((FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n ψ hψ).symm
          (a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n ψ hψ
            (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)))))
  rw [FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_mul_apply χ ψ hχ hψ,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

private theorem composedConjugationQuotientCovariance
    {A V W X : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W) (υ : Representation ℂ A X)
    (α β γ : A → A) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] X)
    (he : ∀ a v, τ a (e v) = e (ρ (α a) v))
    (hf : ∀ a w, υ a (f w) = f (τ (β a) w))
    (hcomp : ∀ a, γ a = α (β a)) :
    ∀ a v, υ a ((e.trans f) v) = (e.trans f) (ρ (γ a) v) := by
  intro a v
  change υ a (f (e v)) = f (e (ρ (γ a) v))
  rw [hf, he, ← hcomp]

private def sameConjugationQuotientEquiv
    {A V W X : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W) (υ : Representation ℂ A X)
    (α : A → A) (e : V ≃ₗ[ℂ] W) (f : V ≃ₗ[ℂ] X)
    (he : ∀ a v, τ a (e v) = e (ρ (α a) v))
    (hf : ∀ a v, υ a (f v) = f (ρ (α a) v)) :
    τ.Equiv υ :=
  Representation.Equiv.mk (e.symm.trans f) (fun a => by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    change f (e.symm (τ a (e v))) = υ a (f (e.symm (e v)))
    rw [he, e.symm_apply_apply, e.symm_apply_apply, hf])

namespace OperatorSubquotient

/-- The actual unit-character quotient map intertwines the unchanged whole action. -/
def determinantTwistOneEquiv (Q : OperatorSubquotient F n) :
    Q.Equivalence (Q.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one) :=
  Representation.Equiv.mk (Q.determinantTwistEquiv 1 HeckeCharacter.hasFiniteOrder_one)
    (fun a => by
      apply LinearMap.ext
      intro f
      exact ((Q.determinantTwistEquiv_operatorAction 1 HeckeCharacter.hasFiniteOrder_one
        a f).trans (congrArg (fun b => Q.determinantTwistEquiv 1
          HeckeCharacter.hasFiniteOrder_one (Q.representation b f))
          (determinantOperatorConjugation_one_apply a))).symm)

@[simp] theorem determinantTwistOneEquiv_apply (Q : OperatorSubquotient F n) (f : Q.Space) :
    Q.determinantTwistOneEquiv f =
      Q.determinantTwistEquiv 1 HeckeCharacter.hasFiniteOrder_one f := rfl

/-- Compare the product and successive actual quotient images by a whole-action equivalence. -/
def determinantTwistMulEquiv (Q : OperatorSubquotient F n)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    (Q.determinantTwist (χ * ψ) (hχ.mul hψ)).Equivalence
      ((Q.determinantTwist χ hχ).determinantTwist ψ hψ) :=
  sameConjugationQuotientEquiv Q.representation
    (Q.determinantTwist (χ * ψ) (hχ.mul hψ)).representation
    ((Q.determinantTwist χ hχ).determinantTwist ψ hψ).representation
    (determinantOperatorConjugation n (χ * ψ) (hχ.mul hψ))
    (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ))
    ((Q.determinantTwistEquiv χ hχ).trans
      ((Q.determinantTwist χ hχ).determinantTwistEquiv ψ hψ))
    (Q.determinantTwistEquiv_operatorAction (χ * ψ) (hχ.mul hψ))
    (composedConjugationQuotientCovariance Q.representation
      (Q.determinantTwist χ hχ).representation
      ((Q.determinantTwist χ hχ).determinantTwist ψ hψ).representation
      (determinantOperatorConjugation n χ hχ)
      (determinantOperatorConjugation n ψ hψ)
      (determinantOperatorConjugation n (χ * ψ) (hχ.mul hψ))
      (Q.determinantTwistEquiv χ hχ)
      ((Q.determinantTwist χ hχ).determinantTwistEquiv ψ hψ)
      (Q.determinantTwistEquiv_operatorAction χ hχ)
      ((Q.determinantTwist χ hχ).determinantTwistEquiv_operatorAction ψ hψ)
      (determinantOperatorConjugation_mul_apply χ ψ hχ hψ))

@[simp] theorem determinantTwistMulEquiv_apply (Q : OperatorSubquotient F n)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder)
    (f : (Q.determinantTwist (χ * ψ) (hχ.mul hψ)).Space) :
    Q.determinantTwistMulEquiv χ ψ hχ hψ f =
      (Q.determinantTwist χ hχ).determinantTwistEquiv ψ hψ
        (Q.determinantTwistEquiv χ hχ
          ((Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ)).symm f)) := rfl

@[simp] theorem determinantTwistMulEquiv_apply_equiv (Q : OperatorSubquotient F n)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder)
    (f : Q.Space) :
    Q.determinantTwistMulEquiv χ ψ hχ hψ
        (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ) f) =
      (Q.determinantTwist χ hχ).determinantTwistEquiv ψ hψ
        (Q.determinantTwistEquiv χ hχ f) := by
  exact (determinantTwistMulEquiv_apply Q χ ψ hχ hψ _).trans
    (congrArg (fun x : Q.Space =>
      (Q.determinantTwist χ hχ).determinantTwistEquiv ψ hψ (Q.determinantTwistEquiv χ hχ x))
      ((Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ)).symm_apply_apply f))

namespace IsoClass

@[simp] theorem determinantTwist_one (c : IsoClass F n) :
    determinantTwist c 1 HeckeCharacter.hasFiniteOrder_one = c := by
  refine Quotient.inductionOn c ?_
  intro Q
  exact ((Q.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one).isoClass_eq_iff Q).mpr
    ⟨Q.determinantTwistOneEquiv.symm⟩

/-- Successive actual quotient twists agree with the product twist on whole-action classes. -/
theorem determinantTwist_mul (c : IsoClass F n)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) ψ hψ =
      determinantTwist c (χ * ψ) (hχ.mul hψ) := by
  refine Quotient.inductionOn c ?_
  intro Q
  exact (((Q.determinantTwist χ hχ).determinantTwist ψ hψ).isoClass_eq_iff
    (Q.determinantTwist (χ * ψ) (hχ.mul hψ))).mpr
      ⟨(Q.determinantTwistMulEquiv χ ψ hχ hψ).symm⟩

/-- The actual finite-order Hecke-character subgroup acts on genuine quotient classes. -/
instance finiteOrderCharacterMulAction :
    MulAction (HeckeCharacter.finiteOrderSubgroup F) (IsoClass F n) where
  smul χ c := determinantTwist c χ.val χ.property
  one_smul := determinantTwist_one
  mul_smul χ ψ c := by
    change determinantTwist c (χ.val * ψ.val) (χ.property.mul ψ.property) =
      determinantTwist (determinantTwist c ψ.val ψ.property) χ.val χ.property
    exact (congrArg (fun η : HeckeCharacter.finiteOrderSubgroup F =>
      determinantTwist c η.val η.property) (mul_comm χ ψ)).trans
        (determinantTwist_mul c ψ.val χ.val ψ.property χ.property).symm

@[simp] theorem finiteOrderCharacter_smul (χ : HeckeCharacter.finiteOrderSubgroup F)
    (c : IsoClass F n) :
    χ • c = determinantTwist c χ.val χ.property := rfl

end IsoClass
end OperatorSubquotient
end Langlands.Automorphic
