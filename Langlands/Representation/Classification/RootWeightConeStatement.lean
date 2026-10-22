import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
The finite inner-product-space cone lemma used in the exhaustion argument for
the Langlands classification. This file defines a proposition; it does not prove it.
-/

namespace Langlands

universe u v

open scoped BigOperators

/--
Silberger's root/weight cone decomposition, in its finite Euclidean formulation.
The root and weight bases are inner-product dual, and distinct roots have
nonpositive inner product. The positive weight support is unique; coefficients
on its complement are nonnegative root coefficients with a minus sign.
-/
def RootWeightConeDecompositionStatement : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (roots weights : Module.Basis ι ℝ E),
    (∀ i j : ι, inner ℝ (roots i) (weights j) = if i = j then 1 else 0) →
    (∀ i j : ι, i ≠ j → inner ℝ (roots i) (roots j) ≤ 0) →
    ∀ x : E, ∃! F : Finset ι,
      ∃ c d : ι → ℝ,
        (∀ i ∈ F, 0 < c i) ∧
        (∀ i ∈ Finset.univ \ F, 0 ≤ d i) ∧
        x = (∑ i ∈ F, c i • weights i) -
          ∑ i ∈ Finset.univ \ F, d i • roots i

end Langlands
