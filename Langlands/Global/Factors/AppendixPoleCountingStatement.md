# Conditional Appendix pole counting

`Langlands.Global.PoleComparison.AppendixPoleCountingStatement` is the
target for a derived version of the pole-counting argument in Henniart
(2000), Appendix A.1–A.3, printed pp.453–454. This module gives the actual
finite complex functions and the proposition definitions; it does not
prove the target or a classification theorem.

For a finite nonempty index type `I`, the segment parameter `length i`
is a natural number, including zero. The corresponding segment has
`length i + 1` terms. `exponent i` is a real number strictly between
`-1/2` and `1/2`. The supplied partner involution preserves the length
and negates the exponent. Applications must construct that involution
from the Hermitian symmetry, including multiplicities and the underlying
unitary labels. No symmetry of multiplicities is inferred from equality
of gamma functions.

`blockLFactor` is the finite product of the actual functions
`base i j`, evaluated at
`z + (length i + length j)/2 - k + exponent i - exponent j`,
for every `i,j` and `0 ≤ k ≤ min (length i) (length j)`.
All shifts are real, embedded in the complex spectral variable.
`blockGamma` is the actual function epsilon times this L-function at
`1-z`, divided by the L-function at `z`.

`BasePairConditions` assumes three distinct properties of the supplied
base functions. At every real point they are meromorphic with
nonpositive order, which also excludes infinite order. At every
positive real point they are holomorphic and nonzero. For the pair
`i, partner i` the base function has strictly negative order at zero.
The intended instance uses unitary supercuspidal pair factors with
matched labels. These conditions, and the assertion that epsilon is
holomorphic and nonzero at every real point, are hypotheses. The module
does not prove the Rankin–Selberg factor formula or its analytic inputs.

The auxiliary shift target sets
`height i = length i / 2 + exponent i`.
For an attained maximum `h`, it asserts `h ≥ 0`, that every occurring
shift is greater than `-1` and at most `2h`, and that the shift `2h`
occurs for a maximal index paired with its partner at `k=0`.
The analytic target asserts that the finite L-product has a pole at
`t = -2h`, its reflected product is holomorphic and nonzero there, and
the gamma expression therefore has positive order there.

This route makes the noncancellation step explicit. At `t=-2h≤0`,
the selected factor has a pole and all other factor orders are
nonpositive, so their finite product still has a pole. At `1-t`,
every shifted real argument is positive because every shift is greater
than `-1`. Hence every numerator factor, and separately epsilon at
`t`, is holomorphic and nonzero. The resulting gamma zero is at
`-2h`. If a separate arithmetic self-pair comparison permits real
gamma zeros only at zero, then `h=0`. Symmetry and the nonnegative
lengths force every length and every exponent to vanish.

The displayed pair-factor product and exponent interval were checked
against the original PDF at Appendix A.2–A.3. The printed discussion
of the most positive pole is not used: the proof target instead uses
the individual shifted arguments and the explicit numerator
holomorphy/nonvanishing condition. This is a derived proof route to
the same vanishing of the segment parameters, not an assertion that
the article separately states the auxiliary bounds.

An actual representation-theoretic application still needs the
unitary-generic classification, the actual finite segment presentation,
the stated pair-factor formula, an epsilon factor, the equality with
the arithmetic self-pair gamma function, and the arithmetic real-zero
restriction. The functional-equation comparison that supplies that
equality must retain its highly ramified stability, existence, and
global boundary nonvanishing inputs. In particular, Shahidi (1981),
Theorem 5.2 is not proved or replaced by the local base-factor
conditions here; its discharge belongs to the parent program
`34b81620-20d7-4059-9b08-6bedd1c1c029` and its common library track.
