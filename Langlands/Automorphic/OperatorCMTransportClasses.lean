import Langlands.Automorphic.OperatorCMTransport

/-! # CM transport of full automorphic equivalences and classes -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance cmClassesRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance cmClassesContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance cmClassesFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance cmClassesFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance cmClassesStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _
local instance cmClassesSpaceGroup (S : OperatorRealization K n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

/-- Inverse image covariance, expressed on an arbitrary vector of the CM image. -/
theorem complexConjEquiv_symm_operatorAction (S : OperatorRealization K n)
    (a : automorphicOperatorAlgebra K n) (f : S.complexConj.Space) :
    S.complexConjEquiv.symm (S.complexConj.representation a f) =
      S.representation (cmOperatorConjugation n a) (S.complexConjEquiv.symm f) := by
  apply S.complexConjEquiv.injective
  exact (S.complexConjEquiv.apply_symm_apply _).trans
    ((congrArg (S.complexConj.representation a)
      (S.complexConjEquiv.apply_symm_apply f).symm).trans
        (S.complexConjEquiv_operatorAction a (S.complexConjEquiv.symm f)))

namespace Intertwiner

variable {S T U : OperatorRealization K n}

/-- Conjugate the actual linear map by the two CM image equivalences. -/
def complexConj (L : S.Intertwiner T) : S.complexConj.Intertwiner T.complexConj where
  toLinearMap := T.complexConjEquiv.toLinearMap.comp
    (L.toLinearMap.comp S.complexConjEquiv.symm.toLinearMap)
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    change T.complexConjEquiv
        (L (S.complexConjEquiv.symm (S.complexConj.representation a f))) =
      T.complexConj.representation a
        (T.complexConjEquiv (L (S.complexConjEquiv.symm f)))
    exact (congrArg (fun x => T.complexConjEquiv (L x))
      (S.complexConjEquiv_symm_operatorAction a f)).trans
        ((congrArg T.complexConjEquiv
          (Representation.IntertwiningMap.isIntertwining S.representation T.representation L
            (cmOperatorConjugation n a) (S.complexConjEquiv.symm f))).trans
          (T.complexConjEquiv_operatorAction a _).symm)

@[simp] theorem complexConj_apply (L : S.Intertwiner T) (f : S.complexConj.Space) :
    L.complexConj f = T.complexConjEquiv (L (S.complexConjEquiv.symm f)) := rfl

@[simp] theorem complexConj_apply_complexConjEquiv (L : S.Intertwiner T) (f : S.Space) :
    L.complexConj (S.complexConjEquiv f) = T.complexConjEquiv (L f) := by
  exact congrArg (fun x => T.complexConjEquiv (L x))
    (S.complexConjEquiv.symm_apply_apply f)

@[simp] theorem complexConj_id (S : OperatorRealization K n) :
    complexConj (S := S) (T := S) (Representation.IntertwiningMap.id S.representation) =
      Representation.IntertwiningMap.id S.complexConj.representation := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change S.complexConjEquiv (S.complexConjEquiv.symm f) = f
  exact S.complexConjEquiv.apply_symm_apply f

theorem complexConj_comp (M : T.Intertwiner U) (L : S.Intertwiner T) :
    complexConj (S := S) (T := U) (M.comp L) = M.complexConj.comp L.complexConj := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change U.complexConjEquiv (M (L (S.complexConjEquiv.symm f))) =
    U.complexConjEquiv
      (M (T.complexConjEquiv.symm
        (T.complexConjEquiv (L (S.complexConjEquiv.symm f)))))
  exact congrArg (fun x => U.complexConjEquiv (M x))
    (T.complexConjEquiv.symm_apply_apply _).symm

end Intertwiner

namespace Equivalence

variable {S T U : OperatorRealization K n}

/-- A full equivalence induces a full equivalence between the actual CM images. -/
def complexConj (e : S.Equivalence T) : S.complexConj.Equivalence T.complexConj :=
  Representation.Equiv.mk
    (S.complexConjEquiv.toLinearEquiv.symm.trans
      (e.toLinearEquiv.trans T.complexConjEquiv.toLinearEquiv))
    (Intertwiner.complexConj (S := S) (T := T) e.toIntertwiningMap).isIntertwining'

@[simp] theorem complexConj_apply (e : S.Equivalence T) (f : S.complexConj.Space) :
    e.complexConj f = T.complexConjEquiv (e (S.complexConjEquiv.symm f)) := rfl

@[simp] theorem complexConj_apply_complexConjEquiv (e : S.Equivalence T) (f : S.Space) :
    e.complexConj (S.complexConjEquiv f) = T.complexConjEquiv (e f) := by
  exact congrArg (fun x => T.complexConjEquiv (e x))
    (S.complexConjEquiv.symm_apply_apply f)

@[simp] theorem complexConj_toIntertwiningMap (e : S.Equivalence T) :
    e.complexConj.toIntertwiningMap =
      Intertwiner.complexConj (S := S) (T := T) e.toIntertwiningMap := rfl

@[simp] theorem complexConj_refl (S : OperatorRealization K n) :
    complexConj (S := S) (T := S) (Representation.Equiv.refl S.representation) =
      Representation.Equiv.refl S.complexConj.representation := by
  apply Representation.Equiv.ext
  funext f
  change S.complexConjEquiv (S.complexConjEquiv.symm f) = f
  exact S.complexConjEquiv.apply_symm_apply f

theorem complexConj_trans (e : S.Equivalence T) (d : T.Equivalence U) :
    complexConj (S := S) (T := U) (e.trans d) = e.complexConj.trans d.complexConj := by
  apply Representation.Equiv.ext
  funext f
  change U.complexConjEquiv (d (e (S.complexConjEquiv.symm f))) =
    U.complexConjEquiv
      (d (T.complexConjEquiv.symm
        (T.complexConjEquiv (e (S.complexConjEquiv.symm f)))))
  exact congrArg (fun x => U.complexConjEquiv (d x))
    (T.complexConjEquiv.symm_apply_apply _).symm

/-- The induced finite-image equivalence uses the same actual CM-transformed map. -/
@[simp] theorem complexConj_finiteImage_apply (e : S.Equivalence T) (f : S.Space) :
    e.complexConj.finiteImage (S.complexConj.finiteEquiv (S.complexConjEquiv f)) =
      T.complexConj.finiteEquiv (T.complexConjEquiv (e f)) := by
  exact (finiteImage_apply e.complexConj (S.complexConjEquiv f)).trans
    (congrArg T.complexConj.finiteEquiv (complexConj_apply_complexConjEquiv e f))

end Equivalence

/-- Actual CM images preserve and reflect the existing full-equivalence relation. -/
theorem complexConj_equivalence_iff {S T : OperatorRealization K n} :
    Nonempty (S.complexConj.Equivalence T.complexConj) ↔ Nonempty (S.Equivalence T) := by
  constructor
  · rintro ⟨e⟩
    have h : Nonempty (S.complexConj.complexConj.Equivalence T.complexConj.complexConj) :=
      ⟨e.complexConj⟩
    simpa only [complexConj_complexConj] using h
  · rintro ⟨e⟩
    exact ⟨e.complexConj⟩

namespace IsoClass

/-- Descent of the actual CM image to full-operator realization classes. -/
def complexConj (c : IsoClass K n) : IsoClass K n :=
  Quotient.lift (s := equivalenceSetoid K n) (fun S => S.complexConj.isoClass)
    (fun S T hST => (S.complexConj.isoClass_eq_iff T.complexConj).mpr
      (complexConj_equivalence_iff.mpr hST)) c

@[simp] theorem complexConj_isoClass (S : OperatorRealization K n) :
    complexConj S.isoClass = S.complexConj.isoClass := rfl

@[simp] theorem complexConj_complexConj (c : IsoClass K n) :
    complexConj (complexConj c) = c := by
  refine Quotient.inductionOn c ?_
  intro S
  change S.complexConj.complexConj.isoClass = S.isoClass
  rw [OperatorRealization.complexConj_complexConj]

/-- CM argument pullback is an involutive permutation of the existing full classes. -/
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
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] {r : ℕ}

namespace IsoClass

/-- CM images descend to the existing positive-rank irreducible cuspidal quotient. -/
def complexConj (c : IsoClass K r) : IsoClass K r :=
  Quotient.lift (s := equivalenceSetoid K r) (fun S => S.complexConj.isoClass)
    (fun S T hST => (S.complexConj.isoClass_eq_iff T.complexConj).mpr
      (OperatorRealization.complexConj_equivalence_iff.mpr hST)) c

@[simp] theorem complexConj_isoClass (S : CuspidalOperatorRealization K r) :
    complexConj S.isoClass = S.complexConj.isoClass := rfl

@[simp] theorem toOperatorClass_complexConj (c : IsoClass K r) :
    (complexConj c).toOperatorClass = c.toOperatorClass.complexConj := by
  refine Quotient.inductionOn c ?_
  intro S
  rfl

@[simp] theorem complexConj_complexConj (c : IsoClass K r) :
    complexConj (complexConj c) = c := by
  apply toOperatorClass_injective
  rw [toOperatorClass_complexConj, toOperatorClass_complexConj,
    OperatorRealization.IsoClass.complexConj_complexConj]

/-- The actual cuspidal class construction has the same involutive inverse. -/
def complexConjEquiv : IsoClass K r ≃ IsoClass K r where
  toFun := complexConj
  invFun := complexConj
  left_inv := complexConj_complexConj
  right_inv := complexConj_complexConj

theorem complexConj_injective : Function.Injective (complexConj (K := K) (r := r)) :=
  complexConjEquiv.injective

@[simp] theorem complexConj_eq_iff (c d : IsoClass K r) :
    complexConj c = complexConj d ↔ c = d := complexConj_injective.eq_iff

end IsoClass
end CuspidalOperatorRealization

namespace PositiveRankCuspidalClass

variable [CompactSpace (AdeleQuotient K)]

/-- Transport the class in its original positive-rank fiber. -/
def complexConj (c : PositiveRankCuspidalClass K) : PositiveRankCuspidalClass K :=
  ⟨c.1, c.2.complexConj⟩

@[simp] theorem rankIndex_complexConj (c : PositiveRankCuspidalClass K) :
    c.complexConj.rankIndex = c.rankIndex := rfl

@[simp] theorem rank_complexConj (c : PositiveRankCuspidalClass K) :
    c.complexConj.rank = c.rank := rfl

@[simp] theorem complexConj_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass K r) :
    (ofFixedRank c).complexConj = ofFixedRank c.complexConj := rfl

@[simp] theorem complexConj_complexConj (c : PositiveRankCuspidalClass K) :
    c.complexConj.complexConj = c := by
  obtain ⟨r, c⟩ := c
  change Sigma.mk r (c.complexConj.complexConj) = Sigma.mk r c
  rw [CuspidalOperatorRealization.IsoClass.complexConj_complexConj]

/-- A rank-preserving involution on the mixed positive-rank classes. -/
def complexConjEquiv : PositiveRankCuspidalClass K ≃ PositiveRankCuspidalClass K where
  toFun := complexConj
  invFun := complexConj
  left_inv := complexConj_complexConj
  right_inv := complexConj_complexConj

theorem complexConj_injective : Function.Injective (complexConj (K := K)) :=
  complexConjEquiv.injective

@[simp] theorem complexConj_eq_iff (c d : PositiveRankCuspidalClass K) :
    c.complexConj = d.complexConj ↔ c = d := complexConj_injective.eq_iff

end PositiveRankCuspidalClass
end Langlands.Automorphic
