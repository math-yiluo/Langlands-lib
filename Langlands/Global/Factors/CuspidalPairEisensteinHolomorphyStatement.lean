import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Factors.CuspidalPairEisensteinSeries
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Continuation and imaginary-axis holomorphy of the generic coefficient of a
cuspidal-pair Eisenstein series

The generic Fourier coefficient of the Eisenstein series on `GL_(r+t+2)` induced from
an actual cuspidal pair continues meromorphically to `ℂ` and is holomorphic on the line
`Re s = 0`. This is the input from Langlands, Bernstein–Lapid (Theorem 2.3 (1)) and
Lapid (2011, Proposition 6) used in Shahidi (1981), proof of Theorem 5.2. See the paired
Markdown for sources, conventions and the relation to the general statements
`EisensteinMeromorphicContinuationStatement` and
`EisensteinImaginaryAxisHolomorphyStatement`. -/

set_option autoImplicit false

universe u

namespace Langlands.Global

open NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters, a standard
additive character `ψ` and a section `φ` of the normalized induced representation from
`π ⊗ π'^∨` on the upper two-block parabolic of `GL_(r+t+2)`, there is a function `Ec`,
meromorphic on `ℂ` and analytic at every point of the imaginary axis, that equals the
generic Fourier coefficient `coeff ψ φ s` of the Eisenstein series on a right half-plane. -/
def CuspidalPairEisensteinHolomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∀ φ, IsSection T T' φ →
    ∃ Ec : ℂ → ℂ, MeromorphicOn Ec Set.univ ∧ (∀ y : ℝ, AnalyticAt ℂ Ec (y * Complex.I)) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Ec s = coeff (r := r) (t := t) ψ φ s

end Langlands.Global
