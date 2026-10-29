import Langlands.Group.GL.UpperBruhatCells
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Lower-left rank characterization of the actual upper Bruhat cells over fields. -/

namespace Langlands.GeneralLinear

universe u

/-- Over every field and in every rank, including zero, an invertible matrix lies in the
actual upper triangular double coset `B * p * B` of the permutation matrix `p` of `w`
exactly when, for all `i j : Fin (n + 1)`, its lower-left corner with rows `r` satisfying
`i ≤ r` and columns `c` satisfying `c < j`, padded by zeros to an `n × n` matrix, has
the same rank as the corresponding padded corner of `p`. -/
def UpperBruhatRankCharacterizationStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (w : Equiv.Perm (Fin n))
    (g : Langlands.GeneralLinear n K),
    g ∈ upperBruhatCell n K w ↔
      ∀ i j : Fin (n + 1),
        Matrix.rank
            ((fun r c => if i.val ≤ r.val ∧ c.val < j.val then g r c else 0 :
              Matrix (Fin n) (Fin n) K)) =
          Matrix.rank
            ((fun r c =>
                if i.val ≤ r.val ∧ c.val < j.val then permutation n K w r c else 0 :
              Matrix (Fin n) (Fin n) K))

end Langlands.GeneralLinear
