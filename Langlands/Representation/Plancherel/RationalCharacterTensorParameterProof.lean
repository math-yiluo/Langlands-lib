import Langlands.Representation.Plancherel.RationalCharacterTensorParameterReduction
import Langlands.Representation.Plancherel.RationalValuationDetection
import Langlands.GroupScheme.Rational.CentralTorusCharacterProof

/-! # Rational-character tensors identify the actual complex image dual

For every connected reductive group over a nonarchimedean local field, the canonical map
`ℂ ⊗[ℤ] X^*(G) → Hom(Λ(G), ℂ)` is bijective. Surjectivity and injectivity under valuation
detection are `rationalCharacterTensorParameterStatement_of_detects`. Valuation detection follows
from the unconditional `GroupScheme.centralTorusCharacter`: a nonzero character restricts
nontrivially to a central torus, hence to some `𝔾_m` in it, and a uniformizer point of that `𝔾_m`
has nonzero valuation.
-/

set_option autoImplicit false

universe u

namespace Langlands.Plancherel

/-- For every connected reductive group over every nonarchimedean local field, complex scalar
extension of rational-character evaluation identifies `ℂ ⊗[ℤ] X^*(G)` with the complex dual of
the actual valuation image. -/
theorem rationalCharacterTensorParameterBijective :
    RationalCharacterTensorParameterStatement.{u} := by
  refine rationalCharacterTensorParameterStatement_of_detects ?_
  intro F _ _ _ _ G hG χ hχ
  exact RationalValuationDetection.exists_rationalCharacterValuation_ne_zero_of_centralTorusCharacter
    GroupScheme.centralTorusCharacter hG hχ

end Langlands.Plancherel
