import Langlands.Correspondence.AssemblyLDatumExistence
import Langlands.LocalFactor.WeilDeligneBlockPair
import Langlands.Weil.Local.ParameterOperations

/-!
# Parameter-side premises of assembled pair L-factor inheritance

The two premises of the reduction of `AssemblyLInheritanceStatement` that concern
only arithmetic pair L-factors of Weil-Deligne representations hold: arithmetic
pair L-factors multiply over finite direct sums (`ArithmeticPairLDirectSum`), and
the pair L-factor of two uncentered special blocks is the product formula of
Henniart 2002, §2.4 (`ArithmeticBlockPairLFactor`). Hence pair L-factor
inheritance follows from JPSS (9.5) for square-integrable data and Henniart's
segment-head L formula alone.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Arithmetic pair L-factors of local Weil-Deligne representations multiply over
finite direct sums in both arguments. -/
theorem arithmeticPairLDirectSum : ArithmeticPairLDirectSum.{uF, uP} F :=
  fun B B' A A' ⟨e⟩ ⟨e'⟩ =>
    LocalFactor.WeilDeligne.pairLFactor_eq_prod_of_equiv_directSum (Weil.Local.localInertia F)
      (Weil.Local.localGeometricFrobenius F) B B' A A' e e'

/-- The arithmetic pair L-factor of two uncentered special blocks is the product of
the arithmetic pair L-factors of the zero-monodromy representations
`ω^(a+b-j) B` and `B'`, `0 ≤ j < min(a + 1, b + 1)`. -/
theorem arithmeticBlockPairLFactor : ArithmeticBlockPairLFactor.{uF, uP} F :=
  fun B B' a b =>
    LocalFactor.WeilDeligne.pairLFactor_block_block _ B B' a b (Weil.Local.localInertia F)
      (Weil.Local.localNormCharacter_on_inertia F) (Weil.Local.localGeometricFrobenius F)

/-- Pair L-factor inheritance of the assembled correspondence follows from JPSS (9.5)
for square-integrable data and Henniart's segment-head L formula. -/
theorem assemblyLInheritance_of_rankinSelberg
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F :=
  assemblyLInheritance_of_rankinSelberg_of_blockPairs F hJ
    (arithmeticPairLDirectSum.{uF, uP} F) hH (arithmeticBlockPairLFactor.{uF, uP} F)

end Langlands.Correspondence
