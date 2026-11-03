import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Reconstruction of bialgebras spanned by group-like elements -/

noncomputable section

universe u v

open Function Module

namespace Langlands

namespace MonoidAlgebra

variable {R : Type u} [CommRing R] [IsDomain R]
  {A : Type v} [Ring A] [Bialgebra R A] [IsTorsionFree R A]

omit [IsDomain R] [IsTorsionFree R A] in
/-- Evaluation of the group algebra on group-like elements is the corresponding
finite linear combination. -/
theorem liftGroupLikeBialgHom_eq_linearCombination
    (x : _root_.MonoidAlgebra R (GroupLike R A)) :
    _root_.MonoidAlgebra.liftGroupLikeBialgHom x =
      Finsupp.linearCombination R (GroupLike.val (R := R) (A := A)) x.coeff := by
  simp [_root_.MonoidAlgebra.liftGroupLikeBialgHom,
    _root_.MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]

/-- Distinct linear combinations of group-like elements remain distinct. -/
theorem liftGroupLikeBialgHom_injective :
    Injective (_root_.MonoidAlgebra.liftGroupLikeBialgHom :
      _root_.MonoidAlgebra R (GroupLike R A) → A) := by
  intro x y hxy
  apply _root_.MonoidAlgebra.coeff_injective
  apply linearIndep_groupLikeVal (R := R) (A := A)
  exact (liftGroupLikeBialgHom_eq_linearCombination x).symm.trans
    (hxy.trans (liftGroupLikeBialgHom_eq_linearCombination y))

omit [IsDomain R] [IsTorsionFree R A] in
/-- Spanning by group-like elements makes the evaluation homomorphism surjective. -/
theorem liftGroupLikeBialgHom_surjective
    (h : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    Surjective (_root_.MonoidAlgebra.liftGroupLikeBialgHom :
      _root_.MonoidAlgebra R (GroupLike R A) → A) := by
  have hr : Set.range (GroupLike.val (R := R) (A := A)) =
      {a : A | IsGroupLikeElem R a} := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact g.isGroupLikeElem_val
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hs : Surjective (Finsupp.linearCombination R
      (GroupLike.val (R := R) (A := A))) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hr, h]
  intro a
  obtain ⟨x, hx⟩ := hs a
  refine ⟨_root_.MonoidAlgebra.ofCoeff x, ?_⟩
  rw [liftGroupLikeBialgHom_eq_linearCombination]
  exact hx

/-- A torsion-free bialgebra over a domain spanned by its group-like elements is
the monoid algebra of those elements, with its full bialgebra structure. -/
def bialgEquivOfSpanGroupLike
    (h : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    _root_.MonoidAlgebra R (GroupLike R A) ≃ₐc[R] A :=
  BialgEquiv.ofBijective _root_.MonoidAlgebra.liftGroupLikeBialgHom
    ⟨liftGroupLikeBialgHom_injective, liftGroupLikeBialgHom_surjective h⟩

@[simp] theorem bialgEquivOfSpanGroupLike_single
    (h : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤)
    (g : GroupLike R A) (r : R) :
    bialgEquivOfSpanGroupLike h (_root_.MonoidAlgebra.single g r) = r • (g : A) := by
  change _root_.MonoidAlgebra.liftGroupLikeBialgHom
    (_root_.MonoidAlgebra.single g r) = _
  simp [_root_.MonoidAlgebra.liftGroupLikeBialgHom]

section Monoid

variable (R) (M : Type v) [Monoid M]

/-- Each monomial gives a group-like element of the monoid algebra. -/
def monomialGroupLikeHom : M →* GroupLike R (_root_.MonoidAlgebra R M) where
  toFun m := ⟨_root_.MonoidAlgebra.single m 1,
    _root_.MonoidAlgebra.isGroupLikeElem_single_one m⟩
  map_one' := GroupLike.val_injective (by simp [_root_.MonoidAlgebra.one_def])
  map_mul' m n := GroupLike.val_injective (by
    simp [_root_.MonoidAlgebra.single_mul_single])

/-- Over a domain, the group-like elements of a monoid algebra are exactly its
monomials, with their original multiplication. -/
def monomialGroupLikeEquiv : M ≃* GroupLike R (_root_.MonoidAlgebra R M) :=
  MulEquiv.ofBijective (monomialGroupLikeHom R M)
    ⟨fun m n hmn => _root_.MonoidAlgebra.single_left_injective one_ne_zero
      (congrArg GroupLike.val hmn), fun g => by
        obtain ⟨m, hm⟩ := _root_.MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp
          g.isGroupLikeElem_val
        exact ⟨m, GroupLike.val_injective hm⟩⟩

@[simp] theorem monomialGroupLikeEquiv_val (m : M) :
    ((monomialGroupLikeEquiv R M m : GroupLike R (_root_.MonoidAlgebra R M)) :
      _root_.MonoidAlgebra R M) = _root_.MonoidAlgebra.single m 1 :=
  rfl

end Monoid

end MonoidAlgebra

end Langlands
