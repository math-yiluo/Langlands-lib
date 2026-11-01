# CM pullback on actual automorphic forms

For an actual number field `K : Type uK` with `NumberField.IsCMField K` and
every natural rank `n`, this internal construction restricts the previously
constructed arithmetic argument pullback to the existing `AutomorphicForms K n`.
The coefficient field is `ℂ`; the pullback is complex-linear and leaves values
unchanged. Rank zero is included.

`isAutomorphicForm_smoothComplexConj_iff` proves preservation and reflection of
all four conditions in `Forms`: a common compact open finite level, finiteness
under the actual standard infinite compact subgroup, simultaneous center
finiteness of the entire slice family, and polynomial growth on each finite
slice. It uses the established arithmetic finite-level equivalence, actual CM
preservation of the standard orthogonal/unitary compact, the whole-family center
transport, and the arithmetic matrix-and-inverse height bound. Constants and
exponents in the growth condition may still depend on the finite slice.

`finiteSmoothComplexConj_mem_automorphic_iff` transfers this result to the
existing common-finite-stabilizer realization. The resulting submodule image
equality lets `AutomorphicForms.complexConj` restrict
`finiteSmoothComplexConj` to a continuous complex-linear equivalence of the
actual form space. Its topology is the existing topology induced successively
from the compact-open continuous-function space.

The value and realization formulas identify this restriction with the actual
ambient pullback. Evaluation is exactly

\[
 (C f)(x)=f(c(x)),
\]

where `c = CMConjugation.adelicConj K n` is the actual arithmetic CM map.
The equivalence is involutive and equals its inverse. Finite translation
transforms by

\[
 C(R(c(d))f)=R(d)(Cf).
\]

The specified finite level becomes its preimage under
`CMConjugation.finiteConj`. The differential formula is the established
arithmetic enveloping covariance on the actual finite-smooth realization.
It does not assert that differentiation preserves the complete automorphic
space.

The central-character membership equivalence sends `χ` to
`χ.complexConj`, with the already established convention
`χ.complexConj x = χ (ideleClassComplexConj x)`.
`CentralCharacterAutomorphicForms.complexConj` is the continuous complex-linear
restriction between exactly these two actual form spaces. Its forward and
inverse realization formulas and finite-translation covariance are proved.
There is no unitary or finite-order assumption on `χ`.

This is derived internal content, assembled from `Forms`, `CuspidalForms`,
`SmoothArithmeticActions`, `CenterFiniteArithmeticTransport` and
`GrowthArithmeticTransport`. It makes no new identification with an original
literature definition and introduces no assumed preservation or existence
theorem. The underlying source-defined automorphic and central-character
conditions are unchanged. Cuspidality, nonzero occurrence, representation-class
transport, and identification of standard compact subgroups for arbitrary
number-field isomorphisms remain separate constructions.
