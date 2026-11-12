import Langlands.Algebra.NondegenerateModuleCenter
import Langlands.Algebra.IdempotentedRingCenterComparison

/-! # The centre of the category of nondegenerate modules (Renard I.1.7)

For a ring with idempotents `A`, the centre `ℨ(A)` of the category `M(A)` of nondegenerate
modules is identified with the commutant of `A` in its completion `Â`, which is the centre of
`Â`, and that centre is the projective limit over the idempotents `e` of the centres of the
corners `eAe`. When `A` is unital, `ℨ(A)` is the centre of `A`.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

/-- Renard I.1.7, the paragraph after the Lemma and the Theorem. Let `A` be a ring with
idempotents (`IsIdempotented A`), `Â = IdempotentedRingRightLimit A` its completion (the
ring of compatible right families, I.1.3) and `M(A)` the category of nondegenerate original
modules, with carriers in a universe containing `A` itself. Then:

* the map sending an element of the commutant of `A` in `Â` to the natural endomorphism of
  the identity functor of `M(A)` by which it acts (the Lemma of I.1.7) is a bijection onto the
  centre `ℨ(A)` of `M(A)`: the two constructions of the paragraph after the Lemma are inverse
  to each other;
* the commutant of `A` in `Â` is the centre of `Â`;
* the maps between the centre of `Â` and the coherent families of central elements of the
  corners `eAe` (`z ↦ (eze)_e` and its converse) are inverse to each other: the centre of
  `Â` is the projective limit of the centres of the `eAe`. -/
def NondegenerateModuleCenterTheoremStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    Function.Bijective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) ∧
    NondegenerateModuleCenter.commutantSubring hA = IdempotentedRingRightLimit.centerSubring hA ∧
    (∀ z : IdempotentedRingRightLimit.Center hA,
      IdempotentedRingCornerCenter.Family.toCenter hA
        (IdempotentedRingRightLimit.Center.toFamily hA z) = z) ∧
    ∀ x : IdempotentedRingCornerCenter.Family A,
      IdempotentedRingRightLimit.Center.toFamily hA
        (IdempotentedRingCornerCenter.Family.toCenter hA x) = x

/-- Renard I.1.7, Remark: when `A` is unital, the centre `ℨ(A)` of the category of
nondegenerate modules (with carriers in a universe containing `A`) is the centre of the ring
`A`. Every central natural endomorphism `θ` of the identity functor is multiplication by a
unique central element `z` of `A` on every module, and every central element arises. -/
def UnitalNondegenerateModuleCenterStatement : Prop :=
  ∀ (A : Type uA) [Ring A],
    (∀ θ : NondegenerateModuleCenter.{uA, max uA uM} A,
      ∃! z : Subring.center A, ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
        (θ.app M).hom.toAddMonoidHom m = (z : A) • m) ∧
    ∀ z : Subring.center A, ∃ θ : NondegenerateModuleCenter.{uA, max uA uM} A,
      ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
        (θ.app M).hom.toAddMonoidHom m = (z : A) • m

end Langlands.Algebra
