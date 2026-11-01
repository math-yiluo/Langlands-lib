import Langlands.Automorphic.OperatorSubquotientDeterminantAction

/-! # Linear transport and natural determinant comparisons on actual quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientDetNaturalityRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientDetNaturalityContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientDetNaturalitySmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientDetNaturalityFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientDetNaturalityStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientDetNaturalityRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

private def inverseConjugationIntertwiner
    {A V W V' W' : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (ρ' : Representation ℂ A V') (τ' : Representation ℂ A W')
    (α : A → A) (hα : Function.Surjective α)
    (e : V ≃ₗ[ℂ] V') (f : W ≃ₗ[ℂ] W')
    (he : ∀ a v, ρ' a (e v) = e (ρ (α a) v))
    (hf : ∀ a w, τ' a (f w) = f (τ (α a) w))
    (L : ρ'.IntertwiningMap τ') : ρ.IntertwiningMap τ where
  toLinearMap := f.symm.toLinearMap.comp (L.toLinearMap.comp e.toLinearMap)
  isIntertwining' a := by
    obtain ⟨b, rfl⟩ := hα a
    apply LinearMap.ext
    intro v
    change f.symm (L (e (ρ (α b) v))) = τ (α b) (f.symm (L (e v)))
    apply f.injective
    rw [f.apply_symm_apply, ← he, ← hf, f.apply_symm_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ L b _

namespace OperatorSubquotient
namespace Intertwiner

variable {Q T U : OperatorSubquotient F n}

/-- Inverse conjugation transports every whole-action map back to the original quotients. -/
def determinantUntwist (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (L : (Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ)) :
    Q.Intertwiner T :=
  inverseConjugationIntertwiner Q.representation T.representation
    (Q.determinantTwist χ hχ).representation (T.determinantTwist χ hχ).representation
    (determinantOperatorConjugation n χ hχ)
    (determinantOperatorConjugation n χ hχ).surjective
    (Q.determinantTwistEquiv χ hχ) (T.determinantTwistEquiv χ hχ)
    (Q.determinantTwistEquiv_operatorAction χ hχ)
    (T.determinantTwistEquiv_operatorAction χ hχ) L

@[simp] theorem determinantUntwist_apply
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (L : (Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ))
    (f : Q.Space) :
    determinantUntwist χ hχ L f =
      (T.determinantTwistEquiv χ hχ).symm (L (Q.determinantTwistEquiv χ hχ f)) := rfl

@[simp] theorem determinantUntwist_determinantTwist (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantUntwist χ hχ (L.determinantTwist χ hχ) = L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (T.determinantTwistEquiv χ hχ).symm
      (T.determinantTwistEquiv χ hχ
        (L ((Q.determinantTwistEquiv χ hχ).symm (Q.determinantTwistEquiv χ hχ f)))) =
    L f
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

@[simp] theorem determinantTwist_determinantUntwist
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (L : (Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ)) :
    (determinantUntwist χ hχ L).determinantTwist χ hχ = L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change T.determinantTwistEquiv χ hχ
      ((T.determinantTwistEquiv χ hχ).symm
        (L (Q.determinantTwistEquiv χ hχ ((Q.determinantTwistEquiv χ hχ).symm f)))) =
    L f
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Actual determinant conjugation is a complex-linear equivalence on the full Hom spaces. -/
def determinantTwistLinearEquiv (Q T : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (Q.Intertwiner T) ≃ₗ[ℂ]
      ((Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ)) where
  toFun L := L.determinantTwist χ hχ
  invFun L := determinantUntwist χ hχ L
  left_inv L := determinantUntwist_determinantTwist L χ hχ
  right_inv L := determinantTwist_determinantUntwist χ hχ L
  map_add' L M := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change T.determinantTwistEquiv χ hχ
        (L ((Q.determinantTwistEquiv χ hχ).symm f) +
          M ((Q.determinantTwistEquiv χ hχ).symm f)) =
      T.determinantTwistEquiv χ hχ (L ((Q.determinantTwistEquiv χ hχ).symm f)) +
        T.determinantTwistEquiv χ hχ (M ((Q.determinantTwistEquiv χ hχ).symm f))
    exact (T.determinantTwistEquiv χ hχ).map_add _ _
  map_smul' c L := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change T.determinantTwistEquiv χ hχ
        (c • L ((Q.determinantTwistEquiv χ hχ).symm f)) =
      c • T.determinantTwistEquiv χ hχ (L ((Q.determinantTwistEquiv χ hχ).symm f))
    exact (T.determinantTwistEquiv χ hχ).map_smul c _

@[simp] theorem determinantTwistLinearEquiv_apply (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwistLinearEquiv Q T χ hχ L = L.determinantTwist χ hχ := rfl

@[simp] theorem determinantTwistLinearEquiv_symm_apply
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (L : (Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ)) :
    (determinantTwistLinearEquiv Q T χ hχ).symm L = determinantUntwist χ hχ L := rfl

theorem determinantTwist_bijective (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Function.Bijective (fun L : Q.Intertwiner T => L.determinantTwist χ hχ) :=
  (determinantTwistLinearEquiv Q T χ hχ).bijective

@[simp] theorem determinantTwist_eq_iff (L M : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    L.determinantTwist χ hχ = M.determinantTwist χ hχ ↔ L = M :=
  (determinantTwistLinearEquiv Q T χ hχ).injective.eq_iff

@[simp] theorem determinantTwist_zero (Q T : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := Q) (T := T) 0 χ hχ = 0 :=
  (determinantTwistLinearEquiv Q T χ hχ).map_zero

@[simp] theorem determinantTwist_eq_zero_iff (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    L.determinantTwist χ hχ = 0 ↔ L = 0 :=
  (determinantTwistLinearEquiv Q T χ hχ).map_eq_zero_iff

/-- The actual unit comparison is natural on genuine whole-action quotient maps. -/
theorem determinantTwist_one_naturality (L : Q.Intertwiner T) :
    (L.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one).comp
        Q.determinantTwistOneEquiv.toIntertwiningMap =
      T.determinantTwistOneEquiv.toIntertwiningMap.comp L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  exact determinantTwist_apply_equiv L 1 HeckeCharacter.hasFiniteOrder_one f

/-- Product comparison commutes with product and successive transports of the same map. -/
theorem determinantTwist_mul_naturality (L : Q.Intertwiner T)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    ((L.determinantTwist χ hχ).determinantTwist ψ hψ).comp
        (Q.determinantTwistMulEquiv χ ψ hχ hψ).toIntertwiningMap =
      (T.determinantTwistMulEquiv χ ψ hχ hψ).toIntertwiningMap.comp
        (L.determinantTwist (χ * ψ) (hχ.mul hψ)) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  refine ((Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ)).surjective.forall
    (p := fun f => (L.determinantTwist χ hχ).determinantTwist ψ hψ
        (Q.determinantTwistMulEquiv χ ψ hχ hψ f) =
      T.determinantTwistMulEquiv χ ψ hχ hψ
        (L.determinantTwist (χ * ψ) (hχ.mul hψ) f))).mpr ?_
  intro v
  change (L.determinantTwist χ hχ).determinantTwist ψ hψ
      (Q.determinantTwistMulEquiv χ ψ hχ hψ
        (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ) v)) =
    T.determinantTwistMulEquiv χ ψ hχ hψ
      (L.determinantTwist (χ * ψ) (hχ.mul hψ)
        (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ) v))
  exact (congrArg
    (fun x => (L.determinantTwist χ hχ).determinantTwist ψ hψ x)
    (Q.determinantTwistMulEquiv_apply_equiv χ ψ hχ hψ v)).trans
      ((determinantTwist_apply_equiv (L.determinantTwist χ hχ) ψ hψ
        (Q.determinantTwistEquiv χ hχ v)).trans
          ((congrArg ((T.determinantTwist χ hχ).determinantTwistEquiv ψ hψ)
            (determinantTwist_apply_equiv L χ hχ v)).trans
              ((T.determinantTwistMulEquiv_apply_equiv χ ψ hχ hψ (L v)).symm.trans
                (congrArg (T.determinantTwistMulEquiv χ ψ hχ hψ)
                  (determinantTwist_apply_equiv L (χ * ψ) (hχ.mul hψ) v).symm))))

end Intertwiner

namespace Equivalence

variable {Q T : OperatorSubquotient F n}

theorem determinantTwist_one_naturality (e : Q.Equivalence T) :
    Q.determinantTwistOneEquiv.trans
        (e.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one) =
      e.trans T.determinantTwistOneEquiv := by
  apply Representation.Equiv.ext
  funext f
  exact determinantTwist_apply_equiv e 1 HeckeCharacter.hasFiniteOrder_one f

theorem determinantTwist_mul_naturality (e : Q.Equivalence T)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    (Q.determinantTwistMulEquiv χ ψ hχ hψ).trans
        ((e.determinantTwist χ hχ).determinantTwist ψ hψ) =
      (e.determinantTwist (χ * ψ) (hχ.mul hψ)).trans
        (T.determinantTwistMulEquiv χ ψ hχ hψ) := by
  apply Representation.Equiv.ext
  apply funext
  refine ((Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ)).surjective.forall
    (p := fun f => (e.determinantTwist χ hχ).determinantTwist ψ hψ
        (Q.determinantTwistMulEquiv χ ψ hχ hψ f) =
      T.determinantTwistMulEquiv χ ψ hχ hψ
        (e.determinantTwist (χ * ψ) (hχ.mul hψ) f))).mpr ?_
  intro v
  change (e.determinantTwist χ hχ).determinantTwist ψ hψ
      (Q.determinantTwistMulEquiv χ ψ hχ hψ
        (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ) v)) =
    T.determinantTwistMulEquiv χ ψ hχ hψ
      (e.determinantTwist (χ * ψ) (hχ.mul hψ)
        (Q.determinantTwistEquiv (χ * ψ) (hχ.mul hψ) v))
  exact (congrArg
    (fun x => (e.determinantTwist χ hχ).determinantTwist ψ hψ x)
    (Q.determinantTwistMulEquiv_apply_equiv χ ψ hχ hψ v)).trans
      ((determinantTwist_apply_equiv (e.determinantTwist χ hχ) ψ hψ
        (Q.determinantTwistEquiv χ hχ v)).trans
          ((congrArg ((T.determinantTwist χ hχ).determinantTwistEquiv ψ hψ)
            (determinantTwist_apply_equiv e χ hχ v)).trans
              ((T.determinantTwistMulEquiv_apply_equiv χ ψ hχ hψ (e v)).symm.trans
                (congrArg (T.determinantTwistMulEquiv χ ψ hχ hψ)
                  (determinantTwist_apply_equiv e (χ * ψ) (hχ.mul hψ) v).symm))))

end Equivalence
end OperatorSubquotient
end Langlands.Automorphic
