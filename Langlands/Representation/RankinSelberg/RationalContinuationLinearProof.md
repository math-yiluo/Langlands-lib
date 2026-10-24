# Finite linear continuation and a fixed denominator

`Langlands.RankinSelberg.rationalContinuationLinear` proves exactly
`RationalContinuationLinearStatement`. This is an internal algebraic
consequence of the existing rational-continuation and Laurent-span
definitions. It does not establish convergence or continuation of any new
integral, or existence of a normalized generator.

The helper lemmas are in `Langlands.RankinSelberg.RationalContinuationLinear`.
The addition, finite-sum, finite-linear-combination, half-plane-transfer,
and span-membership helpers are adapted from Worker 329's shared
`UnequalRankAnalyticProof` draft, revision 3. Worker 64 extracted those
arguments and added closure under the specified denominator and the exact
target assembly. Both workers contributed to this proof.

For addition, the reduced denominator of a sum divides the product of the
input reduced denominators. If the sum denominator vanished at a point
where both input denominators were nonzero, evaluation of this divisibility
would force their product to vanish, a contradiction. The continuation
lemma takes the maximum of the two input real bounds, applies this
nonvanishing fact, and uses rational-function evaluation of addition.
Finite-set induction gives finite sums; the empty sum uses the zero
rational function, whose denominator is one. Applying the published
`hasRationalContinuation_const_mul` termwise yields finite complex linear
combinations, including zero coefficients. Specializing the finite set to
all of `Fin r` proves the first clause of the named statement.

`continuation_of_eq_on_right` intersects a continuation half-plane with
the half-plane on which two complex functions agree. It retains the same
rational function and its denominator nonvanishing.
`linear_combination_mem_span` embeds each complex coefficient as a constant
Laurent polynomial, uses closure of the span under Laurent scalar
multiplication, and sums. These helpers expose the two transfers used
when an actual integral is identified with a finite linear combination.

`denominator_clears_span` proves the second clause by submodule-span
induction. A generating value uses its given Laurent witness. Zero uses
the zero polynomial. If witnesses `P` and `Q` clear `R` and `S`, their sum
clears `R + S`, since the Laurent embedding preserves addition and
multiplication distributes over addition. For a Laurent scalar `a`, the
witness `a * P` clears `a • R`: the scalar action is multiplication by
the actual image of `a`, and commutativity moves that image past the image
of `d`. Every induction step retains the original `d`. There is no
division and no nonzero assumption on `d`.

The auxiliary `commonDenominator_of_mem_span` unpacks a given nonzero
common denominator, applies this fixed-denominator result to a set
contained in the original span, and repackages the same nonzero
denominator. No denominator is inferred merely from individual rationality.
The arguments hold for every natural `q`; they do not use uniqueness of
continuation or require `q > 1`. No independent literature theorem is
claimed.
