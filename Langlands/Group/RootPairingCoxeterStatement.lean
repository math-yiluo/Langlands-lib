import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# The Weyl group of a finite crystallographic root pairing is a Coxeter group

This module states, without proof, that the Weyl group of a finite crystallographic root
pairing over a linearly ordered field is a finite Coxeter group on the reflections in the
simple roots of a regular linear form, with length equal to the number of indivisible
positive roots made negative. It is a Mathlib-native formulation of the classical theorem.
-/

namespace Langlands.Group

/-- For a finite crystallographic root pairing `P` over a linearly ordered field and a linear
form `f` that is nonzero on every root: the Weyl group is finite; it carries a Coxeter system
indexed by the simple roots `IsAddIndecomposable.baseOf P.root f` whose simple generators are
the reflections in those roots; the length of `w` is the number of indivisible roots `α` with
`f α > 0` and `f (w • α) < 0`; and `ℓ(w s_b) > ℓ(w)` exactly when `f (w • P.root b) > 0`.
Nonreduced pairings, rank zero and roots that do not span are included. -/
def RootPairingWeylCoxeterStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (ι : Type u₁) (R : Type u₂) (M : Type u₃) (N : Type u₄)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]
    (f : Module.Dual R M), (∀ i, f (P.root i) ≠ 0) →
    Finite P.weylGroup ∧
    ∃ (Mx : CoxeterMatrix (IsAddIndecomposable.baseOf P.root (f : M →+ R)))
      (cs : CoxeterSystem Mx P.weylGroup),
      (∀ b, cs.simple b = RootPairing.weylGroup.ofIdx P b) ∧
      (∀ w, cs.length w = Set.ncard {i | 0 < f (P.root i) ∧
          (∀ n : ℕ, 2 ≤ n → ∀ j, n • P.root j ≠ P.root i) ∧ f (w • P.root i) < 0}) ∧
      (∀ w b, cs.length w < cs.length (w * cs.simple b) ↔ 0 < f (w • P.root b))

end Langlands.Group
