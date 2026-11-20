# Generic scalar inverse data for actual common-Levi continuations

Multiply the two regular irreducibility factors for induction of the
original inducing object and the inverse-parameter denominator of the
forward dual continuation. Refine the forward continuation by this
nonzero product. At every resulting simultaneous regular parameter,
the original induced fibers are irreducible, and so are the actual
dual induced fibers at the inverse parameter. Compact-test nonvanishing
and Schur's lemma give bijectivity of the three required continued
operators there.

For the two dual continuations, the composite on the source is scalar at
these irreducible fibers. Extract its scalar using a nonzero compact test
vector and a linear functional with value one on that vector. The published
regular-fraction presentation computes the extracted coefficient on the
dual common regular locus. Bijectivity of the two dual maps makes the
scalar nonzero on the refined locus and gives the reverse composition
with the same scalar. Pull back the fraction along parameter inversion.

`genericComparisonDataOfActualContinuations` gives the chosen forward
and reverse dual continuations, the exact scalar inverse data on the
entire genuine locus, and all its density clauses. The compact tensor
is rational there by `GenericComparisonData.rational`. The normalized
original inductions are irreducible on this genuine locus. The variant
`genericComparisonDataOfContinuation` uses the closed common-Levi
continuation statement to supply the three actual continuations.

This internal construction supplies the generic part of Waldspurger
(2003), Lemma V.3.1, printed p. 295, PDF p. 61. Compact-test nonvanishing
and generic irreducibility correspond to IV.1(10) and IV.2.2(i),
printed pp. 283–284, PDF pp. 49–50.
