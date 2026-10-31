# Nonvanishing of an existing square-integrable pair L-polynomial

Authors: Worker 192, with Worker 1067 contributing the exact wrapper binder
pattern.

This module proves
`Langlands.RankinSelberg.SquareIntegrableLPolynomialNonvanishingStatement.{uF,uV,uW}`
as `squareIntegrableLPolynomialNonvanishing`. It supplies the conditional
nonvanishing part of the closed square-integrable pole-freeness goal: every
existing polynomial satisfying the published symmetric pair L-polynomial
relation has no zero in the open unit disk. It does not construct a polynomial.
The theorem introduces the statement's exact quantifiers and applies the
symmetric helper below to the supplied self-dual measure's underlying
additive Haar measure.

The ordered-pair helper chooses a compatible quotient measure from the existence
clause of `IsPadicPairLPolynomial`, then specializes its universal measure
clause to that same measure. At zero the constant coefficient is one, so the
polynomial cannot vanish. At a nonzero point of norm less than one it applies
`IsNormalizedGenerator.eval_ne_zero_of_regularAt` to the actual Laurent span.

For equal ranks, every intrinsic zeta value comes with standard and inverse
Whittaker functions, their functional and coefficient-model membership
witnesses, a Schwartz–Bruhat function, eventual absolute convergence and a
rational-continuation certificate. The published
`squareIntegrableEqualRankAnalytic` applies to those very functionals and model
vectors, giving holomorphy of the same integral on the positive half-plane.
`holomorphicRationalContinuation`, with the residue cardinality strictly greater
than one, makes the rational function regular at the specified nonzero point.

For unequal ranks the existing common-generator relation includes the block
with zero rows. Writing the larger rank parameter as `t + (0 + k + 1)` makes
this generator an `IsUnequalRankLPolynomial` for that block. Its intrinsic value
witnesses give the model vectors needed by
`squareIntegrableZeroRowAnalytic`. The same rational-continuation and generator
regularity argument excludes a root. The impossible descending rank case is
excluded by the definition of the ordered-pair relation. The symmetric helper
uses the existing convention to place the larger rank first and swaps the
representation hypotheses together.

The theorem and helpers retain independent field and carrier universes, the canonical
p-adic topology, the unchanged analytic square-integrability predicate modulo
the center, and the supplied measures. They work for every additive Haar
measure, so in particular for each self-dual measure in the parent target.
No nonzero functional, genericity or multiplicity-one assumption is used:
intrinsic values quantify over all functionals, and the sharp analytic proofs
already handle zero functionals. This proof is internal assembly of the named
published theorems; it makes no new claim of correspondence with an original
source. Factor existence, eventual rationality and common-generator existence
remain separate obligations of the closed parent theorem
`SquareIntegrablePoleFreeStatement`. This conditional result does not prove
that existential statement.

Compilation and declaration inspection with `lean_check` succeed in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no errors or warnings. The inspected
declaration is a theorem with universe parameters `uF`, `uV`, and `uW`; its
only axioms are `propext`, `Classical.choice`, and `Quot.sound`. Independent
semantic review and exact-target validation remain the submission checks.
