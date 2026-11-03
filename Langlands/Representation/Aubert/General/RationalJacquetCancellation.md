# Rational Jacquet compatibility from literal intersection expansion

This internal conditional assembly combines the literal standard intersection
terms with their proved common-term and longest-representative comparisons.
It does not prove the geometric expansion or the whole published
`RationalJacquetCompatibilityStatement`.

`rationalIntersectionExpansion` is the explicit remaining proposition at a
fixed target subset `J`: for every source subset `I` and every section of the
actual normalizer quotient, `r_J i_I` is the sum of
`rationalIntersectionJacquetTerm` over the minimum representatives for `J,I`.
The two fine indices of that actual restricted term are the source intersection
`simpleImage cs w⁻¹ J ∩ I` and target intersection
`simpleImage cs w I ∩ J`, read inside their literal coarse Levis.
The definition supplies no proof of this representation-theoretic equation.

`rationalJacquetCompatibility_of_intersectionExpansion` proves the complete
pointwise Jacquet equation from that one expansion premise. A private choice
lemma constructs a normalizer section attaining the specified arbitrary lift
`n` at `longestRep cs J`. Thus the conclusion retains every such lift and its
actual inverse-conjugation transport.

The proof composes each expansion row with ambient `r_I`.
`rationalIntersectionJacquetTerm_comp_ambient_eq_common` identifies the result
with `rationalCommonJacquetTerm` at `simpleImage cs w I ∩ J`, using actual
normalized Jacquet restriction in stages. Distributing the original alternating
sum gives `jacquetWeightedExpansion`. Its proved weighted cancellation leaves
only the longest representative. `signed_sum_associatedFinsetEquiv` reindexes
the surviving sum by the literal finite subsets of `associatedSubset cs J`.
`rationalJacquetLongestTermReduction` identifies each summand with the
transported associated-Levi term, and `sum_transportedLeviJacquetTerm`
assembles the claimed composite. Every coefficient is the original
`(-1)^|I|`.

`RationalIntersectionExpansionStatement` packages the same literal row
expansion at the complete hypothesis scope of the published target, including
its canonical simple-root enumeration. It derives `hfl` with
`standardParabolicFiniteLength` and every `hLfl` with
`standardLeviParabolicFiniteLength`. Thus their short-exact preservation is
obtained from the existing topological exactness adapters and displayed
finite-length premises.
`rationalJacquetCompatibility_of_intersectionExpansions` is a theorem from
this explicit remaining expansion proposition to the whole unapplied
`RationalJacquetCompatibilityStatement.{u, v}`. It has no other hypothesis or
universe restriction. The expansion proposition itself is not proved here.

The assumptions retain actual rational points, their canonical evaluation
topology, closed ambient Levis and radicals, actual ambient and literal
inside-Levi finite-length and short-exact preservation, standard projection
continuity and compact-limit restricted radicals. Point normalizer and full
centralizer comparisons and the weak point-Coxeter root-sign comparisons are
retained. No scheme Coxeter realization is added. Field and representation
universes remain independent, and representation carriers lie in
`max (u + 1) v`. Empty root sets and empty or full subsets are included.

Provenance is internal: the assembly uses the named normalized stages,
fine-Levi conjugation, common-term, survivor and finite cancellation results.
Worker 1186 supplied the reused standard-intersection/common-term adapter.
No new external assertion is used. The only unproved representation equation
in this module is the explicitly supplied `rationalIntersectionExpansion`;
deriving it from the geometric lemma and actual intersection geometry remains
an obligation of the host task.
