import Langlands.Automorphic.OperatorSubquotientDeterminantTwist
import Langlands.Automorphic.OperatorSubquotientCMTransportClasses

/-! # Determinant transport of actual quotient maps and classes -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientDetClassesRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientDetClassesContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientDetClassesSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientDetClassesFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientDetClassesStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientDetClassesRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

theorem determinantTwistEquiv_symm_operatorAction (Q : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : automorphicOperatorAlgebra F n) (f : (Q.determinantTwist χ hχ).Space) :
    (Q.determinantTwistEquiv χ hχ).symm ((Q.determinantTwist χ hχ).representation a f) =
      Q.representation (determinantOperatorConjugation n χ hχ a)
        ((Q.determinantTwistEquiv χ hχ).symm f) := by
  apply (Q.determinantTwistEquiv χ hχ).injective
  exact ((Q.determinantTwistEquiv χ hχ).apply_symm_apply _).trans
    ((congrArg ((Q.determinantTwist χ hχ).representation a)
      ((Q.determinantTwistEquiv χ hχ).apply_symm_apply f).symm).trans
        (Q.determinantTwistEquiv_operatorAction χ hχ a
          ((Q.determinantTwistEquiv χ hχ).symm f)))

namespace Intertwiner

variable {Q T U : OperatorSubquotient F n}

/-- Conjugate the supplied whole-action map by the actual quotient determinant maps. -/
def determinantTwist (L : Q.Intertwiner T) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (Q.determinantTwist χ hχ).Intertwiner (T.determinantTwist χ hχ) where
  toLinearMap := (T.determinantTwistEquiv χ hχ).toLinearMap.comp
    (L.toLinearMap.comp (Q.determinantTwistEquiv χ hχ).symm.toLinearMap)
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    change T.determinantTwistEquiv χ hχ
        (L ((Q.determinantTwistEquiv χ hχ).symm
          ((Q.determinantTwist χ hχ).representation a f))) =
      (T.determinantTwist χ hχ).representation a
        (T.determinantTwistEquiv χ hχ (L ((Q.determinantTwistEquiv χ hχ).symm f)))
    exact (congrArg (fun x => T.determinantTwistEquiv χ hχ (L x))
      (Q.determinantTwistEquiv_symm_operatorAction χ hχ a f)).trans
        ((congrArg (T.determinantTwistEquiv χ hχ)
          (Representation.IntertwiningMap.isIntertwining Q.representation T.representation L
            (determinantOperatorConjugation n χ hχ a)
            ((Q.determinantTwistEquiv χ hχ).symm f))).trans
          (T.determinantTwistEquiv_operatorAction χ hχ a _).symm)

@[simp] theorem determinantTwist_apply (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : (Q.determinantTwist χ hχ).Space) :
    L.determinantTwist χ hχ f =
      T.determinantTwistEquiv χ hχ (L ((Q.determinantTwistEquiv χ hχ).symm f)) := rfl

@[simp] theorem determinantTwist_apply_equiv (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : Q.Space) :
    L.determinantTwist χ hχ (Q.determinantTwistEquiv χ hχ f) =
      T.determinantTwistEquiv χ hχ (L f) :=
  congrArg (fun x => T.determinantTwistEquiv χ hχ (L x))
    ((Q.determinantTwistEquiv χ hχ).symm_apply_apply f)

@[simp] theorem determinantTwist_id (Q : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := Q) (T := Q) (Representation.IntertwiningMap.id Q.representation)
        χ hχ =
      Representation.IntertwiningMap.id (Q.determinantTwist χ hχ).representation := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change Q.determinantTwistEquiv χ hχ ((Q.determinantTwistEquiv χ hχ).symm f) = f
  exact (Q.determinantTwistEquiv χ hχ).apply_symm_apply f

theorem determinantTwist_comp (M : T.Intertwiner U) (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := Q) (T := U) (M.comp L) χ hχ =
      (M.determinantTwist χ hχ).comp (L.determinantTwist χ hχ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change U.determinantTwistEquiv χ hχ (M (L ((Q.determinantTwistEquiv χ hχ).symm f))) =
    U.determinantTwistEquiv χ hχ
      (M ((T.determinantTwistEquiv χ hχ).symm
        (T.determinantTwistEquiv χ hχ (L ((Q.determinantTwistEquiv χ hχ).symm f)))))
  exact congrArg (fun x => U.determinantTwistEquiv χ hχ (M x))
    ((T.determinantTwistEquiv χ hχ).symm_apply_apply _).symm

set_option maxHeartbeats 800000 in
/-- The inverse-character comparison is natural for actual quotient intertwiners. -/
theorem determinantTwist_inv_naturality (L : Q.Intertwiner T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    ((L.determinantTwist χ hχ).determinantTwist χ⁻¹ hχ.inv).comp
        (Q.determinantTwistInvEquiv χ hχ).toIntertwiningMap =
      (T.determinantTwistInvEquiv χ hχ).toIntertwiningMap.comp L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (L.determinantTwist χ hχ).determinantTwist χ⁻¹ hχ.inv
      ((Q.determinantTwist χ hχ).determinantTwistEquiv χ⁻¹ hχ.inv
        (Q.determinantTwistEquiv χ hχ f)) =
    (T.determinantTwist χ hχ).determinantTwistEquiv χ⁻¹ hχ.inv
      (T.determinantTwistEquiv χ hχ (L f))
  rw [determinantTwist_apply_equiv, determinantTwist_apply_equiv]

end Intertwiner

namespace Equivalence

variable {Q T U : OperatorSubquotient F n}

/-- A supplied whole-action equivalence induces one between actual determinant quotient images. -/
def determinantTwist (e : Q.Equivalence T) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (Q.determinantTwist χ hχ).Equivalence (T.determinantTwist χ hχ) :=
  Representation.Equiv.mk
    ((Q.determinantTwistEquiv χ hχ).symm.trans
      (e.toLinearEquiv.trans (T.determinantTwistEquiv χ hχ)))
    (Intertwiner.determinantTwist (Q := Q) (T := T) e.toIntertwiningMap χ hχ).isIntertwining'

@[simp] theorem determinantTwist_apply (e : Q.Equivalence T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : (Q.determinantTwist χ hχ).Space) :
    e.determinantTwist χ hχ f =
      T.determinantTwistEquiv χ hχ (e ((Q.determinantTwistEquiv χ hχ).symm f)) := rfl

@[simp] theorem determinantTwist_apply_equiv (e : Q.Equivalence T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : Q.Space) :
    e.determinantTwist χ hχ (Q.determinantTwistEquiv χ hχ f) =
      T.determinantTwistEquiv χ hχ (e f) :=
  congrArg (fun x => T.determinantTwistEquiv χ hχ (e x))
    ((Q.determinantTwistEquiv χ hχ).symm_apply_apply f)

@[simp] theorem determinantTwist_toIntertwiningMap (e : Q.Equivalence T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (e.determinantTwist χ hχ).toIntertwiningMap =
      Intertwiner.determinantTwist (Q := Q) (T := T) e.toIntertwiningMap χ hχ := rfl

@[simp] theorem determinantTwist_refl (Q : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := Q) (T := Q) (Representation.Equiv.refl Q.representation) χ hχ =
      Representation.Equiv.refl (Q.determinantTwist χ hχ).representation := by
  apply Representation.Equiv.ext
  funext f
  change Q.determinantTwistEquiv χ hχ ((Q.determinantTwistEquiv χ hχ).symm f) = f
  exact (Q.determinantTwistEquiv χ hχ).apply_symm_apply f

theorem determinantTwist_trans (e : Q.Equivalence T) (d : T.Equivalence U)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := Q) (T := U) (e.trans d) χ hχ =
      (e.determinantTwist χ hχ).trans (d.determinantTwist χ hχ) := by
  apply Representation.Equiv.ext
  funext f
  change U.determinantTwistEquiv χ hχ (d (e ((Q.determinantTwistEquiv χ hχ).symm f))) =
    U.determinantTwistEquiv χ hχ
      (d ((T.determinantTwistEquiv χ hχ).symm
        (T.determinantTwistEquiv χ hχ (e ((Q.determinantTwistEquiv χ hχ).symm f)))))
  exact congrArg (fun x => U.determinantTwistEquiv χ hχ (d x))
    ((T.determinantTwistEquiv χ hχ).symm_apply_apply _).symm

@[simp] theorem determinantTwist_symm (e : Q.Equivalence T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (Q := T) (T := Q) e.symm χ hχ =
      (e.determinantTwist χ hχ).symm := by
  apply Representation.Equiv.ext
  rfl

@[simp] theorem determinantTwist_finiteRestriction_apply (e : Q.Equivalence T)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : Q.Space) :
    (e.determinantTwist χ hχ).finiteRestriction (Q.determinantTwistEquiv χ hχ f) =
      T.determinantTwistEquiv χ hχ (e f) :=
  determinantTwist_apply_equiv e χ hχ f

end Equivalence

/-- Actual determinant quotient transport preserves and reflects whole-action equivalence. -/
theorem determinantTwist_equivalence_iff {Q T : OperatorSubquotient F n}
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Nonempty ((Q.determinantTwist χ hχ).Equivalence (T.determinantTwist χ hχ)) ↔
      Nonempty (Q.Equivalence T) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(Q.determinantTwistInvEquiv χ hχ).trans
      ((e.determinantTwist χ⁻¹ hχ.inv).trans (T.determinantTwistInvEquiv χ hχ).symm)⟩
  · rintro ⟨e⟩
    exact ⟨e.determinantTwist χ hχ⟩

namespace IsoClass

/-- Actual determinant transport descends to classes of genuine whole-operator quotients. -/
def determinantTwist (c : IsoClass F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsoClass F n :=
  Quotient.lift (s := equivalenceSetoid F n) (fun Q => (Q.determinantTwist χ hχ).isoClass)
    (fun Q T hQT => ((Q.determinantTwist χ hχ).isoClass_eq_iff
      (T.determinantTwist χ hχ)).mpr ((determinantTwist_equivalence_iff χ hχ).mpr hQT)) c

@[simp] theorem determinantTwist_isoClass (Q : OperatorSubquotient F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist Q.isoClass χ hχ = (Q.determinantTwist χ hχ).isoClass := rfl

@[simp] theorem determinantTwist_inv (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) χ⁻¹ hχ.inv = c := by
  refine Quotient.inductionOn c ?_
  intro Q
  exact (((Q.determinantTwist χ hχ).determinantTwist χ⁻¹ hχ.inv).isoClass_eq_iff Q).mpr
    ⟨(Q.determinantTwistInvEquiv χ hχ).symm⟩

@[simp] theorem determinantTwist_inv_first (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ⁻¹ hχ.inv) χ hχ = c := by
  have hInv : (⟨χ⁻¹⁻¹, hχ.inv.inv⟩ : {η : HeckeCharacter F // η.HasFiniteOrder}) =
      ⟨χ, hχ⟩ := Subtype.ext (inv_inv χ)
  exact (congrArg
    (fun η : {η : HeckeCharacter F // η.HasFiniteOrder} =>
      determinantTwist (determinantTwist c χ⁻¹ hχ.inv) η.val η.property)
    hInv).symm.trans (determinantTwist_inv c χ⁻¹ hχ.inv)

/-- Finite-order determinant transport is a permutation, inverted by the inverse character. -/
def determinantTwistEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsoClass F n ≃ IsoClass F n where
  toFun c := determinantTwist c χ hχ
  invFun c := determinantTwist c χ⁻¹ hχ.inv
  left_inv c := determinantTwist_inv c χ hχ
  right_inv c := determinantTwist_inv_first c χ hχ

@[simp] theorem determinantTwistEquiv_apply (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwistEquiv χ hχ c = determinantTwist c χ hχ := rfl

@[simp] theorem determinantTwistEquiv_symm_apply (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (determinantTwistEquiv χ hχ).symm c = determinantTwist c χ⁻¹ hχ.inv := rfl

theorem determinantTwist_injective (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Function.Injective (fun c : IsoClass F n => determinantTwist c χ hχ) :=
  (determinantTwistEquiv χ hχ).injective

@[simp] theorem determinantTwist_eq_iff (c d : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist c χ hχ = determinantTwist d χ hχ ↔ c = d :=
  (determinantTwist_injective χ hχ).eq_iff

end IsoClass
end OperatorSubquotient
end Langlands.Automorphic
