import Langlands.GroupScheme.Commutative.MultiplicativeUnipotentDecompositionStatement
import Langlands.GroupScheme.Commutative.MultiplicativePartCharacteristic
import Langlands.GroupScheme.Commutative.MultiplicativeUnipotentUniqueness
import Langlands.GroupScheme.Commutative.MultiplicativeUnipotentSplitting

/-! # Multiplicative and unipotent parts of a commutative algebraic group (Milne 16.13)

Part (a) is `CommutativeDecomposition.exists_characteristic_multiplicativePart`. Part (b)
combines the existence theorem `CommutativeDecomposition.exists_multiplicativeUnipotentDecomposition`
with the uniqueness theorems `CommutativeDecomposition.range_le_of_isUnipotent` and
`CommutativeDecomposition.range_le_of_isMultiplicativeType`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Milne 2017, Theorem 16.13.** Multiplicative and unipotent parts of a commutative affine
algebraic group over a field. -/
theorem commutativeMultiplicativeUnipotentDecomposition :
    CommutativeMultiplicativeUnipotentDecompositionStatement.{u} := by
  intro k _ G _ _ _
  refine ⟨CommutativeDecomposition.exists_characteristic_multiplicativePart G, fun _ => ?_⟩
  refine ⟨CommutativeDecomposition.exists_multiplicativeUnipotentDecomposition G, ?_⟩
  intro U S u s hu hU hs hS hiso
  let := hiso
  exact ⟨fun V j hj hV => CommutativeDecomposition.range_le_of_isUnipotent u s hS j hj hV,
    fun H h _ hH => CommutativeDecomposition.range_le_of_isMultiplicativeType u s hu hU h hH⟩

end Langlands.GroupScheme
