# Binomial denominator bounds from central translation

This is a derived algebraic supporting module for the equal-rank supercuspidal
L-factor problem. It does not prove regularity of any integral.

`CentralShiftLaw C a c m` is the recurrence

`c · C(v,w,a φ) = X^m · C(v,w,φ)`

for an actual complex-trilinear rational family `C`, a linear test operator `a`,
a complex scalar `c`, and a natural exponent `m`. The definition itself requires
neither `c` nor `m` to be nonzero. In the intended application, `a` translates a
row test by an inverse central uniformizer, `c` is the product of the two central
character values, and `m` is the positive determinant exponent. These
interpretations are not premises hidden in the definition.

`CentralShiftLaw.clears` assumes a linear functional `e` with `e(a φ) = e(φ)`,
and Laurent regularity of every value whose test lies in `ker e`. The difference
`a φ - φ` lies in that kernel. Multiplying its Laurent representative by `c`
and using the recurrence shows that `X^m - c` clears every value of `C`.
This implication also holds when `c` or `m` is zero.

`IsNormalizedGenerator.dvd_of_clears` says that a nonzero polynomial `D`
clearing all generating values is divisible by their normalized polynomial `P`.
The proof extends clearing to the Laurent span using the published
`RationalContinuationLinear.denominator_clears_span`, applies it to `1/P`,
and obtains Laurent-span membership in the span of `1/D`.
The published normalized reciprocal divisibility criterion gives `P ∣ D`.

`CentralShiftLaw.normalizedGenerator_bound` combines these two results.
It assumes that every specified generating value occurs in the trilinear
family, that `P` is the normalized generator of their Laurent span, and that
`c ≠ 0` and `m ≠ 0`. It proves

`P ∣ X^m - c`, `P.Separable`, and `Squarefree P`.

Over the complex numbers the binomial is separable by the characteristic-zero
separability theorem for `X^m - c`; separability passes to its divisor `P`.
Thus the conclusion excludes repeated roots of `P`. The argument neither
identifies these roots with contragredient twists nor proves the converse
existence of a pole for each twist.

All ingredients are internal deductions from the published Laurent embedding,
normalized-generator definition, denominator-span closure, polynomial
divisibility criterion, and Mathlib's separability theorem. No external
mathematical assertion is introduced. For an analytic application, the central
recurrence and the Laurent regularity on `ker e` must still be proved.
