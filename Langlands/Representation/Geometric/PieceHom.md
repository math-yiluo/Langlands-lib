# A nonzero induction map from one geometric piece

This internal deduction combines the published normalized geometric lemma,
preservation of admissibility, the full Levi cuspidal constituent theorem and
the orbit-map half of Frobenius reciprocity. It adds no classification
assumption.

`Geometric.exists_ne_zero_to_induced_of_piece` assumes admissible smooth source
Levi data, irreducible cuspidal smooth target Levi data, and a minimal double-coset
representative. For any actual intersection refinements attached to that
representative, the supplied premise must identify its geometric piece with the
target representation. The conclusion is a nonzero intertwiner from normalized
induction of the source to normalized induction of the target. Field, source
carrier and target carrier universes are independent.

The proof evaluates the geometric-lemma filtration at the source and selects
the specified representative using the filtration's enumeration. The supplied
piece equivalence identifies the corresponding graded representation with the
target. Induction and Jacquet functors preserve admissibility. The existing
`exists_ne_zero_of_gradedRepresentation_equiv` then applies the Levi constituent
theorem to obtain an actual quotient map from the Jacquet module to that
cuspidal constituent, and Frobenius reciprocity produces the required nonzero
map of inductions. In particular, a graded constituent is not silently treated
as a quotient without the admissibility and cuspidality hypotheses.

`Geometric.exists_minimal_matching_of_sorted` is an elementary combinatorial
companion. Source and target tuples with equal multisets have a matching
permutation by the existing finite-occurrence matching theorem. A ranking into
any linear order is assumed strictly increasing on each source block and
weakly increasing on the target tuple; target blocks all have size one.
Weak target monotonicity reflects each strict source-ranking inequality to a
strict inequality of matched target positions. The inverse-order condition is
automatic on singleton target blocks. Thus the matching permutation is a
minimal representative. Repeated target values and equal rankings of distinct
values are permitted; no distinctness hypothesis is used.

`Geometric.nonzeroInductionMapOfPiece` packages this existence argument as an
actual chosen nonzero intertwiner, together with its nonvanishing proof. Its
assumptions are precisely those of `exists_ne_zero_to_induced_of_piece`.
