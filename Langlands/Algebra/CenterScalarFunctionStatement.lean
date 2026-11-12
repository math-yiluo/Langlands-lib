import Langlands.Algebra.NondegenerateModuleCenter
import Langlands.Algebra.NondegenerateScalars
import Mathlib.LinearAlgebra.Dimension.Basic

/-! # The centre as an algebra of functions on the irreducibles (Renard I.1.8)

For a complex algebra with idempotents of at most countable dimension, every element of
the centre `ℨ(A)` of the category of nondegenerate modules acts on each simple module by a
scalar, which depends only on the isomorphism class (the map (I.1.8.1)). Under the
separation property (Sep), the action of the completion `Â` on the simple modules is
faithful (the extension of (I.1.8.2) to `Â` is injective), so an element of `ℨ(A)` is
determined by its function on the simple modules.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

/-- Renard I.1.8. Let `A` be a complex algebra with idempotents of finite or countable
dimension, and let `M(A)` be its category of nondegenerate modules, with carriers in a universe
containing `A`. A module `M` is simple when it is nonzero and its only submodules are `0` and
`M`. The complex scalars on a nondegenerate module are the canonical ones of I.2.1
(`NondegenerateScalars.scalarMul`). Then:

* every `z ∈ ℨ(A)` acts on every simple `M` as multiplication by a unique scalar `z_M`;
* `z_M = z_N` when `M ≅ N`, so (I.1.8.1) `z ↦ [M ↦ z_M]` is defined on isomorphism
  classes;
* under (Sep), every nonzero `a ∈ A` acts nontrivially on some simple module: then every
  nonzero element of the completion `Â` acts nontrivially on some simple module (the
  extension of (I.1.8.2) to `Â` is injective), and two elements of `ℨ(A)` with the same
  scalars on every simple module are equal. -/
def CenterScalarFunctionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A],
    IsIdempotented A → Module.rank ℂ A ≤ Cardinal.aleph0 →
    let IsSimple : NondegenerateModuleCat.{uA, max uA uM} A → Prop := fun M =>
      Nontrivial M.obj ∧
        ∀ S : NonUnitalSubmodule A M.obj, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
    let acts : NondegenerateModuleCenter.{uA, max uA uM} A →
        (M : NondegenerateModuleCat.{uA, max uA uM} A) → M.obj → M.obj :=
      fun z M m => (z.app M).hom.toAddMonoidHom m
    (∀ (z : NondegenerateModuleCenter.{uA, max uA uM} A)
        (M : NondegenerateModuleCat.{uA, max uA uM} A), IsSimple M →
        ∃! c : ℂ, ∀ m : M.obj, acts z M m = NondegenerateScalars.scalarMul ℂ M.property c m) ∧
    (∀ (z : NondegenerateModuleCenter.{uA, max uA uM} A)
        (M N : NondegenerateModuleCat.{uA, max uA uM} A), Nonempty (M ≅ N) → IsSimple M → IsSimple N →
        ∀ c : ℂ, (∀ m : M.obj, acts z M m = NondegenerateScalars.scalarMul ℂ M.property c m) →
          ∀ n : N.obj, acts z N n = NondegenerateScalars.scalarMul ℂ N.property c n) ∧
    ((∀ a : A, a ≠ 0 → ∃ M : NondegenerateModuleCat.{uA, max uA uM} A,
        IsSimple M ∧ ∃ m : M.obj, a • m ≠ 0) →
      (∀ x : IdempotentedRingRightLimit A,
        (∀ M : NondegenerateModuleCat.{uA, max uA uM} A, IsSimple M →
          ∀ m : M.obj, IdempotentedRingRightLimitAction.act M.property x m = 0) → x = 0) ∧
      ∀ z z' : NondegenerateModuleCenter.{uA, max uA uM} A,
        (∀ M : NondegenerateModuleCat.{uA, max uA uM} A, IsSimple M →
          ∀ m : M.obj, acts z M m = acts z' M m) → z = z')

end Langlands.Algebra
