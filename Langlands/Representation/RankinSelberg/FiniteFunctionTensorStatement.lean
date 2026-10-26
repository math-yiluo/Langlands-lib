import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite tensor expansions of continuous translation-finite functions

This proposition generalizes the finite-function tensor reduction on p-adic
tori used in JPSS (1983), printed page 392 before display (6), to a monoid
with an arbitrary topology. It asserts no analytic conclusion.
-/

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uG

/-- A continuous function with finite-dimensional left-translation span on a
finite power of a monoid is a finite linear combination of products of
one-variable functions satisfying the same condition. -/
def FiniteFunctionTensorStatement : Prop :=
  ∀ (G : Type uG) [Monoid G] [TopologicalSpace G] (r : ℕ),
    let finiteOne := fun h : G → ℂ =>
      Continuous h ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : G => fun a : G => h (b * a)))
    let finiteProduct := fun h : (Fin r → G) → ℂ =>
      Continuous h ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fin r → G => fun a : Fin r → G => h (b * a)))
    ∀ η : (Fin r → G) → ℂ, finiteProduct η →
      ∃ (N : ℕ) (c : Fin N → ℂ) (f : Fin N → Fin r → G → ℂ),
        (∀ j i, finiteOne (f j i)) ∧
        ∀ a : Fin r → G, η a = ∑ j : Fin N, c j * ∏ i : Fin r, f j i (a i)

end Langlands.RankinSelberg
