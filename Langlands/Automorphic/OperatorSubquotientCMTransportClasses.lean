import Langlands.Automorphic.OperatorSubquotientCMTransport

/-! # CM transport of actual quotient intertwiners and classes -/

noncomputable section
universe uK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance quotientCMClassesRationalGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMClassesContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMClassesSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMClassesFormGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance quotientCMClassesStableGroup : AddCommGroup (StableAutomorphicFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMClassesRealizationGroup (S : OperatorRealization K n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

/-- A linear map intertwining every concrete operator on the actual quotients. -/
abbrev Intertwiner (Q T : OperatorSubquotient K n) :=
  Q.representation.IntertwiningMap T.representation

theorem complexConjEquiv_symm_operatorAction (Q : OperatorSubquotient K n)
    (a : automorphicOperatorAlgebra K n) (f : Q.complexConj.Space) :
    Q.complexConjEquiv.symm (Q.complexConj.representation a f) =
      Q.representation (cmOperatorConjugation n a) (Q.complexConjEquiv.symm f) := by
  apply Q.complexConjEquiv.injective
  exact (Q.complexConjEquiv.apply_symm_apply _).trans
    ((congrArg (Q.complexConj.representation a)
      (Q.complexConjEquiv.apply_symm_apply f).symm).trans
        (Q.complexConjEquiv_operatorAction a (Q.complexConjEquiv.symm f)))

namespace Intertwiner

variable {Q T U : OperatorSubquotient K n}

/-- Conjugate the supplied map by the actual induced quotient CM equivalences. -/
def complexConj (L : Q.Intertwiner T) : Q.complexConj.Intertwiner T.complexConj where
  toLinearMap := T.complexConjEquiv.toLinearMap.comp
    (L.toLinearMap.comp Q.complexConjEquiv.symm.toLinearMap)
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    change T.complexConjEquiv
        (L (Q.complexConjEquiv.symm (Q.complexConj.representation a f))) =
      T.complexConj.representation a
        (T.complexConjEquiv (L (Q.complexConjEquiv.symm f)))
    exact (congrArg (fun x => T.complexConjEquiv (L x))
      (Q.complexConjEquiv_symm_operatorAction a f)).trans
        ((congrArg T.complexConjEquiv
          (Representation.IntertwiningMap.isIntertwining Q.representation T.representation L
            (cmOperatorConjugation n a) (Q.complexConjEquiv.symm f))).trans
          (T.complexConjEquiv_operatorAction a _).symm)

@[simp] theorem complexConj_apply (L : Q.Intertwiner T) (f : Q.complexConj.Space) :
    L.complexConj f = T.complexConjEquiv (L (Q.complexConjEquiv.symm f)) := rfl

@[simp] theorem complexConj_apply_complexConjEquiv (L : Q.Intertwiner T) (f : Q.Space) :
    L.complexConj (Q.complexConjEquiv f) = T.complexConjEquiv (L f) :=
  congrArg (fun x => T.complexConjEquiv (L x)) (Q.complexConjEquiv.symm_apply_apply f)

@[simp] theorem complexConj_id (Q : OperatorSubquotient K n) :
    complexConj (Q := Q) (T := Q) (Representation.IntertwiningMap.id Q.representation) =
      Representation.IntertwiningMap.id Q.complexConj.representation := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change Q.complexConjEquiv (Q.complexConjEquiv.symm f) = f
  exact Q.complexConjEquiv.apply_symm_apply f

theorem complexConj_comp (M : T.Intertwiner U) (L : Q.Intertwiner T) :
    complexConj (Q := Q) (T := U) (M.comp L) = M.complexConj.comp L.complexConj := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change U.complexConjEquiv (M (L (Q.complexConjEquiv.symm f))) =
    U.complexConjEquiv
      (M (T.complexConjEquiv.symm
        (T.complexConjEquiv (L (Q.complexConjEquiv.symm f)))))
  exact congrArg (fun x => U.complexConjEquiv (M x))
    (T.complexConjEquiv.symm_apply_apply _).symm

set_option maxHeartbeats 800000 in
/-- Twice transport is naturally identified with the original intertwiner. -/
theorem complexConj_twice_naturality (L : Q.Intertwiner T) :
    L.complexConj.complexConj.comp Q.complexConjTwiceEquiv.toIntertwiningMap =
      T.complexConjTwiceEquiv.toIntertwiningMap.comp L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change L.complexConj.complexConj (Q.complexConj.complexConjEquiv (Q.complexConjEquiv f)) =
    T.complexConj.complexConjEquiv (T.complexConjEquiv (L f))
  rw [complexConj_apply_complexConjEquiv, complexConj_apply_complexConjEquiv]

end Intertwiner

namespace Equivalence

variable {Q T U : OperatorSubquotient K n}

/-- A whole-action equivalence induces one between the actual CM quotient images. -/
def complexConj (e : Q.Equivalence T) : Q.complexConj.Equivalence T.complexConj :=
  Representation.Equiv.mk
    (Q.complexConjEquiv.symm.trans (e.toLinearEquiv.trans T.complexConjEquiv))
    (Intertwiner.complexConj (Q := Q) (T := T) e.toIntertwiningMap).isIntertwining'

@[simp] theorem complexConj_apply (e : Q.Equivalence T) (f : Q.complexConj.Space) :
    e.complexConj f = T.complexConjEquiv (e (Q.complexConjEquiv.symm f)) := rfl

@[simp] theorem complexConj_apply_complexConjEquiv (e : Q.Equivalence T) (f : Q.Space) :
    e.complexConj (Q.complexConjEquiv f) = T.complexConjEquiv (e f) :=
  congrArg (fun x => T.complexConjEquiv (e x)) (Q.complexConjEquiv.symm_apply_apply f)

@[simp] theorem complexConj_toIntertwiningMap (e : Q.Equivalence T) :
    e.complexConj.toIntertwiningMap =
      Intertwiner.complexConj (Q := Q) (T := T) e.toIntertwiningMap := rfl

@[simp] theorem complexConj_refl (Q : OperatorSubquotient K n) :
    complexConj (Q := Q) (T := Q) (Representation.Equiv.refl Q.representation) =
      Representation.Equiv.refl Q.complexConj.representation := by
  apply Representation.Equiv.ext
  funext f
  change Q.complexConjEquiv (Q.complexConjEquiv.symm f) = f
  exact Q.complexConjEquiv.apply_symm_apply f

theorem complexConj_trans (e : Q.Equivalence T) (d : T.Equivalence U) :
    complexConj (Q := Q) (T := U) (e.trans d) = e.complexConj.trans d.complexConj := by
  apply Representation.Equiv.ext
  funext f
  change U.complexConjEquiv (d (e (Q.complexConjEquiv.symm f))) =
    U.complexConjEquiv
      (d (T.complexConjEquiv.symm
        (T.complexConjEquiv (e (Q.complexConjEquiv.symm f)))))
  exact congrArg (fun x => U.complexConjEquiv (d x))
    (T.complexConjEquiv.symm_apply_apply _).symm

@[simp] theorem complexConj_symm (e : Q.Equivalence T) :
    complexConj (Q := T) (T := Q) e.symm = e.complexConj.symm := by
  apply Representation.Equiv.ext
  rfl

@[simp] theorem complexConj_finiteRestriction_apply (e : Q.Equivalence T) (f : Q.Space) :
    e.complexConj.finiteRestriction (Q.complexConjEquiv f) =
      T.complexConjEquiv (e f) :=
  complexConj_apply_complexConjEquiv e f

end Equivalence

/-- The actual CM quotient construction preserves and reflects whole-action equivalence. -/
theorem complexConj_equivalence_iff {Q T : OperatorSubquotient K n} :
    Nonempty (Q.complexConj.Equivalence T.complexConj) ↔ Nonempty (Q.Equivalence T) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Q.complexConjTwiceEquiv.trans (e.complexConj.trans T.complexConjTwiceEquiv.symm)⟩
  · rintro ⟨e⟩
    exact ⟨e.complexConj⟩

namespace IsoClass

/-- CM transport descends to classes of actual whole-operator quotients. -/
def complexConj (c : IsoClass K n) : IsoClass K n :=
  Quotient.lift (s := equivalenceSetoid K n) (fun Q => Q.complexConj.isoClass)
    (fun Q T hQT => (Q.complexConj.isoClass_eq_iff T.complexConj).mpr
      (complexConj_equivalence_iff.mpr hQT)) c

@[simp] theorem complexConj_isoClass (Q : OperatorSubquotient K n) :
    complexConj Q.isoClass = Q.complexConj.isoClass := rfl

@[simp] theorem complexConj_complexConj (c : IsoClass K n) :
    complexConj (complexConj c) = c := by
  refine Quotient.inductionOn c ?_
  intro Q
  exact (Q.complexConj.complexConj.isoClass_eq_iff Q).mpr ⟨Q.complexConjTwiceEquiv.symm⟩

/-- The involutive permutation retains the entire concrete operator action. -/
def complexConjEquiv : IsoClass K n ≃ IsoClass K n where
  toFun := complexConj
  invFun := complexConj
  left_inv := complexConj_complexConj
  right_inv := complexConj_complexConj

theorem complexConj_injective : Function.Injective (complexConj (K := K) (n := n)) :=
  complexConjEquiv.injective

@[simp] theorem complexConj_eq_iff (c d : IsoClass K n) :
    complexConj c = complexConj d ↔ c = d := complexConj_injective.eq_iff

end IsoClass
end OperatorSubquotient
end Langlands.Automorphic
