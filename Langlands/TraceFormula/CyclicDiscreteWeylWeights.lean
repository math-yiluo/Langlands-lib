import Langlands.Group.GL.Blocks
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Order.Partition.Finpartition

/-! # Levi and Weyl coefficients in the prime cyclic discrete trace identity -/

noncomputable section

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.TraceFormula

/-- A coordinate partition labels a Levi subgroup containing the diagonal torus of `GL_n`.
The individual blocks are nonempty and are not ordered. -/
abbrev CoordinateLevi (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))

namespace CoordinateLevi

variable {n : ℕ} (M : CoordinateLevi n)

/-- The blocks of the coordinate partition. -/
abbrev Block : Type := {b : Finset (Fin n) // b ∈ M.parts}

/-- The order of the Weyl group of the ambient diagonal torus in the Levi. -/
def internalWeylOrder : ℕ := ∏ b : M.Block, b.val.card.factorial

/-- The relative Weyl permutations of the Levi blocks are exactly the size-preserving ones. -/
def IsRelativeWeyl (s : Equiv.Perm M.Block) : Prop := ∀ b, (s b).val.card = b.val.card

/-- A full-space matrix for the determinant of `s - 1` on the split-component quotient.
On the constant line it is the identity, by addition of the averaging projection. -/
def quotientWeylMatrix (s : Equiv.Perm M.Block) : Matrix M.Block M.Block ℝ :=
  fun i j => (if i = s j then 1 else 0) - (if i = j then 1 else 0) + (M.parts.card : ℝ)⁻¹

/-- The absolute relative determinant in the discrete trace coefficient. -/
def regularDeterminant (s : Equiv.Perm M.Block) : ℝ := |(M.quotientWeylMatrix s).det|

/-- The finite set of size-preserving Weyl elements regular on the split-component quotient. -/
def regularWeyl : Finset (Equiv.Perm M.Block) := by
  classical
  exact Finset.univ.filter (fun s => M.IsRelativeWeyl s ∧ M.regularDeterminant s ≠ 0)

/-- The coefficient multiplying an unweighted operator trace in II.(9.2) and III.(4.1)–(4.2). -/
def discreteWeight (s : Equiv.Perm M.Block) : ℝ :=
  (M.internalWeylOrder : ℝ) / (n.factorial : ℝ) * (M.regularDeterminant s)⁻¹

end CoordinateLevi

/-- Every regular Weyl element is a full block cycle, with determinant equal to the
number of blocks. The one-block Levi has determinant one. -/
def CyclicRegularWeylDeterminantStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (M : CoordinateLevi n) (s : Equiv.Perm M.Block),
    (M.regularDeterminant s ≠ 0 ↔ s.IsCycleOn Set.univ) ∧
    (s.IsCycleOn Set.univ → M.regularDeterminant s = (M.parts.card : ℝ))

/-- For `l` blocks of size `m`, the number of coordinate Levis times the internal and
relative Weyl orders equals the ambient Weyl order. -/
def CyclicEqualBlockLeviCountStatement : Prop := by
  classical
  exact ∀ (m l : ℕ), 0 < m → 0 < l →
    let levis := (Finset.univ : Finset (CoordinateLevi (m * l))).filter fun M =>
      M.parts.card = l ∧ ∀ b : M.Block, b.val.card = m
    levis.card * (m.factorial ^ l) * l.factorial = (m * l).factorial

end Langlands.TraceFormula
