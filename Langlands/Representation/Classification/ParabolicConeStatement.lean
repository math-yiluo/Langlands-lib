import Langlands.Group.GL.Blocks
import Mathlib.Basic.Real.Basic

/-!
# Root/weight cone decomposition in actual GL block coordinates

This is the parabolic specialization of Silberger 1978, Lemma 7.1, with
the arbitrary central direction restored. It is a proposition definition.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uR

/-- A unique consecutive coarsening has strictly decreasing averaged
determinant exponents and nonpositive residual partial sums inside each new
block. The resulting actual parabolic and Levi contain the original ones. -/
def GLParabolicRootWeightConeStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (r : Fin B.length → ℝ),
    ∃! C : BlockShape n,
      ∃ (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ),
        Monotone q ∧ Function.Surjective q ∧
        (∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i) ∧
        StrictAnti t ∧
        (∀ j, (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) =
          (C.size j : ℝ) * t j) ∧
        (∀ i, (∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
          (r k - (B.size k : ℝ) * t (q i))) ≤ 0) ∧
        (∀ (R : Type uR) [CommRing R],
          B.parabolic R ≤ C.parabolic R ∧
          B.leviSubgroup R ≤ C.leviSubgroup R)

end Langlands
