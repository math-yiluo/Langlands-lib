import Langlands.CommutativeAlgebra.CompleteLocalNormalizationFiniteness
import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
import StacksFrontier.RingTheory.Nagata.Defs
import StacksFrontier.RingTheory.Nagata.FiniteType

/-! # Proof of universal Japanese finiteness over a complete local ring from the Stacks copy -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Proof of `CompleteLocalNormalizationFinitenessStatement`: a Noetherian local ring complete at
its maximal ideal is Nagata (Stacks Project, Tag 032W, the copy's
`StacksIsNagataRing.of_isPrecomplete_maximalIdeal`), hence universally Japanese (Tag 0334, the
copy's `isNagataRing_tfae`), and the Japanese property of the domain `S` of finite type over it is
the finiteness asked for. -/
theorem completeLocalNormalizationFiniteness :
    CompleteLocalNormalizationFinitenessStatement.{u} := by
  intro R _ _ _ _ S _ _ _ _ L _ _ _ _ _
  have hR : StacksIsNagataRing R := StacksIsNagataRing.of_isPrecomplete_maximalIdeal
  have hU : IsUniversallyJapaneseRing R ∧ IsNoetherianRing R :=
    ((isNagataRing_tfae (R := R)).out 1 3).mp hR
  exact (hU.1.japanese S).finite L

end Langlands.CommutativeAlgebra
