import Langlands.Group.GL.UpperBruhatCells
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Homeomorph.Defs

/-!
# The plus-minus multiplication homeomorphism of the upper unipotent group

The statement only; see the paired Markdown for the source, the internal
Hausdorff topological-field generalization and the conventions.
-/

namespace Langlands.GeneralLinear

universe u

/-- For every Hausdorff topological field `K`, rank `n` and permutation `w`,
some homeomorphism `U_w⁺ × U_w⁻ ≃ₜ U` has underlying matrix `u⁺ * u⁻` at every
pair `(u⁺, u⁻)`, for the actual plus, minus and upper unipotent subgroups. -/
def UpperUnipotentFactorizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
    ∃ e : (permutationUnipotentPlus n K w × permutationUnipotentMinus n K w) ≃ₜ
        upperUnipotent n K,
      ∀ x : permutationUnipotentPlus n K w × permutationUnipotentMinus n K w,
        (e x).val = x.1.val * x.2.val

end Langlands.GeneralLinear
