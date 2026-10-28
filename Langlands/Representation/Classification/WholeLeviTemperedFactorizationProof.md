# Tempered factorization of arbitrary whole-Levi inputs

Author: Worker 403.

`Langlands.glWholeLeviTemperedFactorization` proves the exact closed proposition
`Langlands.GLWholeLeviTemperedFactorizationStatement.{uF,uV}` from
[WholeLeviTemperedFactorizationStatement](WholeLeviTemperedFactorizationStatement.md).
It retains the independent field and carrier universes and returns every
factor in the input carrier universe.

Fix the target's prime, actual p-adic field, supplied topological data, positive
total rank and arbitrary ordered block shape. Install the supplied field
topology. The input is an arbitrary representation `σ` of the full actual Levi;
its only hypotheses are algebraic irreducibility and the existing
`RelativeRegularComparison.IsLeviTempered` predicate.

The implemented proof uses four published results:

1. `RelativeRegularComparison.IsLeviTempered.isAdmissible` from
   [RelativeCosocleAdmissibilityProof](RelativeCosocleAdmissibilityProof.md)
   derives `IsAdmissible σ.ρ`. That theorem uses existence of a Borel Haar
   measure on the actual quotient by the full Levi center, so the universal
   analytic predicate supplies admissibility without a further hypothesis.
   Its smoothness conjunct bundles the same carrier and action as `σsmooth`
   via `SmoothRep.of`.
2. `CuspidalSupport.padicLeviAdmissibleFactorization.{uF,uV}` from
   [LeviAdmissibleFactorizationProof](../CuspidalSupport/LeviAdmissibleFactorizationProof.md)
   applies to this irreducible admissible smooth representation. It produces
   smooth block factors `A`, their irreducibility and admissibility, and an
   actual representation equivalence `e` directed from `σ.ρ` to their
   external tensor. Bundling the input changes neither its action nor its
   carrier.
3. `T.isLeviTempered_iff_of_equiv` from
   [InnerLeviTransport](../Induction/InnerLeviTransport.md) transports the
   input's exact whole-Levi temperedness along `e` to the tensor, bundled
   algebraically using `Rep.of`. Its conclusion quantifies over the same
   measurable and Borel realizations and every Haar measure on the actual
   Levi central quotient.
4. The reverse implication of the proved
   `Langlands.glBlockTensorTempered.{uF,uV}` from
   [BlockTensorTemperedProof](BlockTensorTemperedProof.md) gives
   `T.IsTempered (A i).representation` for every factor. Its hypotheses are
   exactly the irreducibility and admissibility already obtained in step 2.
   The tensor condition in that theorem is definitionally the whole-Levi
   predicate obtained in step 3.

The resulting existential returns the four target conjuncts in order:
factorwise irreducibility, admissibility, analytic temperedness, and
`Nonempty` of the actual equivalence from the original representation to
the external tensor.

This is an internal derivation from the published results above and the
unchanged target, whose Markdown records the provenance of the algebraic and
analytic ingredients. No claim is made that a single original source states
this dependent-type formulation. The proof adds no smoothness, admissibility,
factorization, unitary form, central character, countability or universe
domination premise. Positive rank and the supplied block shape are passed
unchanged to the algebraic and analytic theorems, including the one-block case.
The proof uses no semistandard conjugacy, regular recovery, parameter
uniqueness or downstream classification conclusion.
